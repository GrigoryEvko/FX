import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen

/-! # Tools/StrictHarness — aggregate strict-discipline gates

The existing `#assert_no_axioms` and `#audit_namespace` commands fail
fast on the first violation.  This module adds **aggregate** gates
that report every violation in one pass, plus detect several
discipline failures beyond raw axioms:

* `noncomputable` markers (banned for kernel theorems)
* `@[extern]` / `@[implemented_by]` attributes (hide computational
  meaning behind native code)
* Direct references to `Classical.*` constants (even non-axiom uses
  are suspect at the kernel layer)

The aggregate gate `#audit_namespace_strict` walks a namespace, classifies
every auditable declaration's violations, and emits a single error
listing all offending decls when any are found.  The summary surface
makes failures impossible to miss in noisy build output.

The parity gate `#assert_raw_typed_parity` walks two inductives and
verifies that every constructor of the first has a same-suffix
constructor in the second.  Used to enforce raw-layer / typed-layer
parity for `RawStep.par` and `Step.par`.

The FX1 host-minimal gate `#assert_fx1_core_host_minimal` checks that
the minimal root namespace does not depend on host-heavy Lean modules
or forbidden host axioms.  It is intentionally stricter than the
project-wide gate because FX1/Core is the planned trusted root.

The import-surface gates keep public production imports, host imports,
FX1 imports, rich-production-to-FX1 imports, redundant direct project imports,
public-umbrella reachability, and the legacy Lean-kernel scaffold from
accidentally collapsing into one dependency cone.
-/

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Strict violation taxonomy -/

/-- A single discipline violation against a kernel declaration. -/
inductive StrictViolation : Type
  /-- The declaration's transitive closure includes a Lean axiom or
  user-declared axiom of the given name. -/
  | leakedAxiom (axiomName : Name) : StrictViolation
  /-- The declaration is marked `noncomputable`. -/
  | markedNoncomputable : StrictViolation
  /-- The declaration carries the `@[extern]` attribute, hiding kernel
  computation behind a native-code shim. -/
  | externAttribute : StrictViolation
  /-- The declaration carries the `@[implemented_by]` attribute. -/
  | implementedByAttribute : StrictViolation
  /-- The declaration's transitive closure references a `Classical.*`
  symbol other than `Classical.choice` (which is already flagged as
  an axiom). -/
  | classicalReference (referenceName : Name) : StrictViolation
  deriving Inhabited, Repr

/-- Render one violation for a build-error message. -/
def StrictViolation.format : StrictViolation → String
  | .leakedAxiom axiomName => s!"axiom {axiomName}"
  | .markedNoncomputable => "noncomputable"
  | .externAttribute => "@[extern]"
  | .implementedByAttribute => "@[implemented_by]"
  | .classicalReference referenceName => s!"Classical reference {referenceName}"

/-- Render a list of violations comma-separated. -/
def formatViolationList (violations : Array StrictViolation) : String :=
  String.intercalate ", " (violations.toList.map StrictViolation.format)

/-! ## Detection helpers -/

/-- Detect direct references to `Classical.*` constants other than
`Classical.choice` (already caught as an axiom). -/
def collectClassicalReferences
    (environment : Environment) (someName : Name) :
    Array Name :=
  let dependencyNames := collectDependencies environment someName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun classicalSoFar dependencyName =>
      if (`Classical).isPrefixOf dependencyName &&
          dependencyName != `Classical.choice then
        classicalSoFar.push dependencyName
      else
        classicalSoFar)

/-- Collect transitive dependencies carrying Lean's `@[extern]` attribute. -/
def collectExternDependencies
    (environment : Environment) (someName : Name) :
    Array Name :=
  let dependencyNames := collectDependencies environment someName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun externSoFar dependencyName =>
      if (Lean.externAttr.getParam? environment dependencyName).isSome then
        externSoFar.push dependencyName
      else
        externSoFar)

/-- Build-failing transitive extern-dependency gate for one declaration.

This is stricter than the namespace-level strict audit, which flags extern
attributes on project declarations themselves.  Use this for executable
trusted-root primitives where depending on host runtime code would widen the
TCB even when the declaration remains axiom-clean. -/
elab "#assert_no_extern_dependencies " targetSyntax:ident : command => do
  let environment ← getEnv
  let targetName := targetSyntax.getId
  match environment.find? targetName with
  | none =>
      throwError "unknown declaration for extern audit: {targetName}"
  | some _ =>
      let externDependencies := collectExternDependencies environment targetName
      if externDependencies.isEmpty then
        logInfo m!"{targetName} : no extern dependencies"
      else
        let renderedDependencies :=
          String.intercalate ", " (externDependencies.toList.map toString)
        throwError
          s!"{targetName} depends on extern declarations: [{renderedDependencies}]"

/-- Compute every strict-discipline violation for one declaration.
Built up by appending each violation category in turn so we avoid a
do-block / `let mut` shape (which the parser rejects in this `def`
position) and make the order of checks self-documenting. -/
def classifyStrictViolations
    (environment : Environment) (someName : Name) (someInfo : ConstantInfo) :
    Array StrictViolation :=
  let _ := someInfo
  -- Axiom dependencies (transitive closure includes Lean core axioms).
  let stats := computeStats environment someName (includeStdlib := true)
  let axiomViolations : Array StrictViolation :=
    stats.axiomNames.map StrictViolation.leakedAxiom
  -- Noncomputable marker on the declaration itself.
  let noncomputableViolations : Array StrictViolation :=
    if Lean.isNoncomputable environment someName then
      #[StrictViolation.markedNoncomputable]
    else
      #[]
  -- @[extern] / @[implemented_by] attributes hide computational meaning
  -- behind native code; treat as discipline violations for kernel decls.
  let externViolations : Array StrictViolation :=
    if (Lean.externAttr.getParam? environment someName).isSome then
      #[StrictViolation.externAttribute]
    else
      #[]
  let implementedByViolations : Array StrictViolation :=
    if (Lean.Compiler.implementedByAttr.getParam? environment someName).isSome then
      #[StrictViolation.implementedByAttribute]
    else
      #[]
  -- Direct references to `Classical.*` constants (excluding
  -- `Classical.choice`, already counted as an axiom dependency).
  let classicalViolations : Array StrictViolation :=
    (collectClassicalReferences environment someName).map
      StrictViolation.classicalReference
  axiomViolations ++ noncomputableViolations ++ externViolations ++
    implementedByViolations ++ classicalViolations

/-! ## Aggregate strict gates -/

/-- Aggregate strict gate.  Walks a namespace, classifies every
auditable declaration's violations, and emits a single error listing
all offenders.  This is the **load-bearing** strict gate.  Use it in
`Tools/AuditAll.lean` per kernel namespace. -/
elab "#audit_namespace_strict " namespaceSyntax:ident : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violationsByDecl : Array (Name × Array StrictViolation) := #[]
  for targetName in targetNames do
    match environment.find? targetName with
    | none => continue
    | some constantInfo =>
        let violations := classifyStrictViolations environment targetName constantInfo
        if !violations.isEmpty then
          violationsByDecl := violationsByDecl.push (targetName, violations)
  if violationsByDecl.isEmpty then
    logInfo m!"strict audit ok: {namespaceName} ({targetNames.size} declarations)"
  else
    let perDeclLines :=
      violationsByDecl.toList.map fun (someName, violations) =>
        s!"  ✗ {someName}: {formatViolationList violations}"
    let header :=
      s!"strict audit FAILED for {namespaceName}: " ++
      s!"{violationsByDecl.size} of {targetNames.size} decls violate discipline"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-- Aggregate strict gate variant that includes `LeanFX2.Smoke`
declarations.  Used by `Smoke/AuditNamespace.lean`. -/
elab "#audit_namespace_strict_including_smoke " namespaceSyntax:ident : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let targetNames := namespaceAuditTargetsIncludingSmoke environment namespaceName
  let mut violationsByDecl : Array (Name × Array StrictViolation) := #[]
  for targetName in targetNames do
    match environment.find? targetName with
    | none => continue
    | some constantInfo =>
        let violations := classifyStrictViolations environment targetName constantInfo
        if !violations.isEmpty then
          violationsByDecl := violationsByDecl.push (targetName, violations)
  if violationsByDecl.isEmpty then
    logInfo m!"strict audit ok including smoke: {namespaceName} ({targetNames.size} declarations)"
  else
    let perDeclLines :=
      violationsByDecl.toList.map fun (someName, violations) =>
        s!"  ✗ {someName}: {formatViolationList violations}"
    let header :=
      s!"strict audit FAILED for {namespaceName}: " ++
      s!"{violationsByDecl.size} of {targetNames.size} decls violate discipline"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## FX1/Core host-minimal dependency gate -/

/-- Host dependencies forbidden inside FX1/Core.

This gate deliberately checks dependency names, not source imports.  The
project-wide build environment may contain `Lean` or `Std` because the audit
tools themselves use elaborator APIs; FX1/Core declarations must not depend on
those symbols in their type or value dependency closure. -/
def isForbiddenFX1HostDependency (dependencyName : Name) : Bool :=
  (`Lean).isPrefixOf dependencyName ||
  (`Std).isPrefixOf dependencyName ||
  (`Classical).isPrefixOf dependencyName ||
  (`Quot).isPrefixOf dependencyName ||
  dependencyName == `propext ||
  dependencyName == `Classical.choice ||
  dependencyName == `Quot.sound ||
  dependencyName == `Quot.lift ||
  dependencyName == `sorryAx

/-- Collect forbidden host dependencies for one FX1/Core declaration. -/
def collectForbiddenFX1HostDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames := collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun forbiddenSoFar dependencyName =>
      if isForbiddenFX1HostDependency dependencyName then
        forbiddenSoFar.push dependencyName
      else
        forbiddenSoFar)

/-- Build-failing FX1/Core host-minimal gate.  Walks the given namespace and
flags every declaration whose dependency closure mentions `Lean`, `Std`,
`Classical`, host `Quot`, `propext`, `Classical.choice`, `Quot.sound`,
`Quot.lift`, or `sorryAx`.

Use this for `LeanFX2.FX1` once the minimal root namespace is imported by the
build.  With zero declarations it still logs success, which lets the gate be
wired before the namespace exists. -/
elab "#assert_fx1_core_host_minimal " namespaceSyntax:ident : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array (Name × Array Name) := #[]
  for targetName in targetNames do
    let forbiddenDependencies :=
      collectForbiddenFX1HostDependencies environment targetName
    if !forbiddenDependencies.isEmpty then
      violations := violations.push (targetName, forbiddenDependencies)
  if violations.isEmpty then
    logInfo m!"FX1 host-minimal audit ok: {namespaceName} ({targetNames.size} declarations)"
  else
    let perDeclLines := violations.toList.map fun (declName, dependencies) =>
      let renderedDependencies :=
        String.intercalate ", " (dependencies.toList.map toString)
      s!"  - {declName}: forbidden host dependencies [{renderedDependencies}]"
    let header :=
      s!"FX1 host-minimal audit FAILED for {namespaceName}: " ++
      s!"{violations.size} of {targetNames.size} decls violate host policy"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Import-surface gates -/

/-- The pre-FX1 Lean-kernel scaffold namespace.  It remains buildable and
audited, but it is not the planned trusted Lean-in-FX path. -/
def isLegacyLeanKernelScaffoldModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.Lean.Kernel).isPrefixOf moduleName

/-- Deliberate host-boundary modules.  These are buildable and visible to
the broad import census, but they are outside the zero-axiom production
umbrella because their job is to cross host APIs explicitly. -/
def isHostBoundaryModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Surface.HostLex

/-- Modules allowed to import explicit host-boundary shims directly. -/
def mayImportHostBoundaryModule (sourceModuleName : Name) : Bool :=
  isHostBoundaryModuleName sourceModuleName ||
    (`LeanFX2.Tools).isPrefixOf sourceModuleName ||
    (`LeanFX2.Smoke).isPrefixOf sourceModuleName

/-- Modules that are public production-bearing LeanFX2 modules rather than
tests, tooling, sketches, or the old Lean-kernel scaffold.  This includes the
root `LeanFX2` umbrella so `import LeanFX2` itself stays clean. -/
def isProductionLeanFX2ModuleName (moduleName : Name) : Bool :=
  (`LeanFX2).isPrefixOf moduleName &&
    !(`LeanFX2.Smoke).isPrefixOf moduleName &&
    !(`LeanFX2.Tools).isPrefixOf moduleName &&
    !(`LeanFX2.Sketch).isPrefixOf moduleName &&
    !isHostBoundaryModuleName moduleName &&
    !isLegacyLeanKernelScaffoldModuleName moduleName

/-- Imports that production modules must not take directly.

`Smoke` and `Tools` are allowed to depend on production code; production code
must not depend on them.  `Sketch` is proof-of-concept space.  The root
`LeanFX2` umbrella is the public import surface and must not be used as an
internal dependency. -/
def isForbiddenProductionImportModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.Smoke).isPrefixOf moduleName ||
    (`LeanFX2.Tools).isPrefixOf moduleName ||
    (`LeanFX2.Sketch).isPrefixOf moduleName ||
    moduleName == `LeanFX2

/-- Direct forbidden imports for one imported module. -/
def forbiddenProductionImportsForModule
    (moduleData : ModuleData) : Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun forbiddenImports directImport =>
      if isForbiddenProductionImportModuleName directImport.module then
        forbiddenImports.push directImport.module
      else
        forbiddenImports)

/-- Build-failing import-surface gate.  It checks direct imports for every
production `LeanFX2.*` module visible in the current environment. -/
elab "#assert_production_import_surface_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedProductionModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isProductionLeanFX2ModuleName moduleName then
      scannedProductionModules := scannedProductionModules + 1
      let forbiddenImports := forbiddenProductionImportsForModule moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (moduleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"production import surface ok: {scannedProductionModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: forbidden direct imports [{renderedImports}]"
    let header :=
      s!"production import surface FAILED: " ++
      s!"{violations.size} of {scannedProductionModules} production modules violate import policy"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## Rich production host-import discipline -/

/-- Rich production modules are the regular `LeanFX2` kernel/product modules,
excluding the future FX1 trusted-root namespace.  FX1 has its own stricter
source-import policy below, because it intentionally permits `Init.Prelude` as
the only host import during the bootstrap phase. -/
def isRichProductionLeanFX2ModuleName (moduleName : Name) : Bool :=
  isProductionLeanFX2ModuleName moduleName &&
    !(`LeanFX2.FX1).isPrefixOf moduleName

/-- Host-heavy modules that rich production source files must not import
directly.

This is a source-level gate, not a declaration-dependency gate.  It catches
unused broad host imports before any declaration can depend on them.

Lean records an implicit `Init` import for every module in `ModuleData`, so
`Init` cannot be distinguished here from an explicit source import.  The
declaration-dependency gates still catch forbidden axiom use from `Init`, while
this import gate focuses on broad host APIs such as `Lean` and `Std`. -/
def isForbiddenRichProductionHostImportModuleName (moduleName : Name) : Bool :=
  (`Lean).isPrefixOf moduleName ||
    (`Lake).isPrefixOf moduleName ||
    (`Std).isPrefixOf moduleName ||
    (`Mathlib).isPrefixOf moduleName ||
    (`Classical).isPrefixOf moduleName ||
    (`Quot).isPrefixOf moduleName

/-- Direct host imports forbidden for one rich production module. -/
def forbiddenRichProductionHostImportsForModule
    (moduleData : ModuleData) : Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun forbiddenImports directImport =>
      if isForbiddenRichProductionHostImportModuleName directImport.module then
        forbiddenImports.push directImport.module
      else
        forbiddenImports)

/-- Build-failing gate for rich production modules that import host-heavy
modules directly.  Tooling may import `Lean`; FX1 may import `Init.Prelude`;
regular production modules must stay inside the project import cone apart from
Lean's ambient `Init` prelude. -/
elab "#assert_rich_production_host_import_surface_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedRichProductionModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isRichProductionLeanFX2ModuleName moduleName then
      scannedRichProductionModules := scannedRichProductionModules + 1
      let forbiddenImports :=
        forbiddenRichProductionHostImportsForModule moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (moduleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"rich production host-import surface ok: {scannedRichProductionModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: forbidden host imports [{renderedImports}]"
    let header :=
      s!"rich production host-import surface FAILED: " ++
      s!"{violations.size} of {scannedRichProductionModules} modules import host modules directly"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## Explicit host-boundary isolation -/

/-- Host-boundary direct imports that cross out of the allowed
smoke/tool/boundary cone. -/
def forbiddenHostBoundaryImportsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun forbiddenImports directImport =>
      if isHostBoundaryModuleName directImport.module &&
          !mayImportHostBoundaryModule sourceModuleName then
        forbiddenImports.push directImport.module
      else
        forbiddenImports)

/-- Build-failing isolation gate for explicit host-boundary modules.

Host-boundary modules remain buildable and visible in the import census, but
regular production modules and the public `LeanFX2` umbrella must not import
them directly.  Smoke and tooling may import them to test and audit the
boundary. -/
elab "#assert_host_boundary_isolated" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf moduleName then
      scannedModules := scannedModules + 1
      let forbiddenImports :=
        forbiddenHostBoundaryImportsForModule moduleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (moduleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"host-boundary isolation ok: {scannedModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: forbidden host-boundary imports [{renderedImports}]"
    let header :=
      s!"host-boundary isolation FAILED: " ++
      s!"{violations.size} of {scannedModules} modules import host-boundary shims"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## FX1 direct-import discipline -/

/-- FX1/Core modules are the planned minimal root calculus. -/
def isFX1CoreModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.FX1.Core).isPrefixOf moduleName

/-- FX1/LeanKernel modules encode Lean's kernel over FX1/Core. -/
def isFX1LeanKernelModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.FX1.LeanKernel).isPrefixOf moduleName

/-- Any module under the future FX1 namespace. -/
def isFX1ModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.FX1).isPrefixOf moduleName

/-! ## Direct import records -/

/-- One direct source-module import edge. -/
structure DirectImportRecord where
  /-- Module that contains the import declaration. -/
  sourceModuleName : Name
  /-- Module named by the import declaration. -/
  importedModuleName : Name
  deriving Inhabited, Repr

/-- Render one direct import edge for compact build-log summaries. -/
def DirectImportRecord.format (directImportRecord : DirectImportRecord) :
    String :=
  s!"{directImportRecord.sourceModuleName} -> " ++
    s!"{directImportRecord.importedModuleName}"

/-- Keep summary lines bounded while still naming the exact dependency
edges when the count is small. -/
def formatDirectImportRecords
    (directImportRecords : Array DirectImportRecord) :
    String :=
  if directImportRecords.isEmpty then
    "none"
  else
    String.intercalate "; "
      (directImportRecords.toList.map DirectImportRecord.format)

/-! ## Public umbrella isolation -/

/-- Public umbrella modules that should remain entrypoints, not convenient
internal dependencies.

Layer roots such as `LeanFX2.Term` are real implementation modules in this
repository.  This list is intentionally narrower: it contains only the broad
entrypoint surfaces whose accidental use inside production code would collapse
the dependency graph. -/
def isPublicUmbrellaImportModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2 ||
    moduleName == `LeanFX2.Kernel ||
    moduleName == `LeanFX2.Rich ||
    moduleName == `LeanFX2.FX1 ||
    moduleName == `LeanFX2.FX1.Core

/-- Direct public-umbrella imports that are part of the intended entrypoint
chain rather than internal dependency shortcuts. -/
def isAllowedPublicUmbrellaImport
    (directImportRecord : DirectImportRecord) :
    Bool :=
  (directImportRecord.sourceModuleName == `LeanFX2 &&
      directImportRecord.importedModuleName == `LeanFX2.Rich) ||
    (directImportRecord.sourceModuleName == `LeanFX2.Rich &&
      directImportRecord.importedModuleName == `LeanFX2.Kernel) ||
    (directImportRecord.sourceModuleName == `LeanFX2.FX1 &&
      directImportRecord.importedModuleName == `LeanFX2.FX1.Core) ||
    (`LeanFX2.Tools).isPrefixOf directImportRecord.sourceModuleName ||
    (`LeanFX2.Smoke).isPrefixOf directImportRecord.sourceModuleName

/-- Public-umbrella imports that violate the entrypoint discipline for one
module. -/
def publicUmbrellaImportViolationsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array DirectImportRecord :=
  moduleData.imports.foldl
    (init := (#[] : Array DirectImportRecord))
    (fun violations directImport =>
      let directImportRecord : DirectImportRecord := {
        sourceModuleName := sourceModuleName
        importedModuleName := directImport.module
      }
      if isPublicUmbrellaImportModuleName directImport.module &&
          !isAllowedPublicUmbrellaImport directImportRecord then
        violations.push directImportRecord
      else
        violations)

/-- Build-failing gate that keeps broad public umbrellas out of internal
dependencies.

The allowed edges are the public entrypoint chain itself
(`LeanFX2 -> Rich`, `Rich -> Kernel`, `FX1 -> FX1.Core`) plus smoke/tooling
audits.  Production implementation modules must import the narrow module they
actually need. -/
elab "#assert_public_umbrella_imports_isolated" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLeanFX2Modules : Nat := 0
  let mut violations : Array DirectImportRecord := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf sourceModuleName then
      scannedLeanFX2Modules := scannedLeanFX2Modules + 1
      violations :=
        violations ++
          publicUmbrellaImportViolationsForModule sourceModuleName moduleData
  if violations.isEmpty then
    logInfo m!"public umbrella import isolation ok: {scannedLeanFX2Modules} modules"
  else
    let renderedImports := formatDirectImportRecords violations
    let header :=
      s!"public umbrella import isolation FAILED: " ++
      s!"{violations.size} forbidden broad imports"
    throwError (header ++ "\n  " ++ renderedImports)

/-! ## Rich production / FX1 separation -/

/-- Direct FX1 imports from one rich production module. -/
def forbiddenRichProductionFX1ImportsForModule
    (moduleData : ModuleData) : Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun forbiddenImports directImport =>
      if isFX1ModuleName directImport.module then
        forbiddenImports.push directImport.module
      else
        forbiddenImports)

/-- Build-failing gate that keeps the rich production engine from importing
FX1 directly.  FX1 is the future minimal trusted root, so rich modules must not
silently depend on it before an explicit bridge/certificate layer exists. -/
elab "#assert_rich_production_fx1_import_surface_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedRichProductionModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isRichProductionLeanFX2ModuleName moduleName then
      scannedRichProductionModules := scannedRichProductionModules + 1
      let forbiddenImports :=
        forbiddenRichProductionFX1ImportsForModule moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (moduleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"rich production FX1-import surface ok: {scannedRichProductionModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: forbidden FX1 imports [{renderedImports}]"
    let header :=
      s!"rich production FX1-import surface FAILED: " ++
      s!"{violations.size} of {scannedRichProductionModules} modules import FX1 directly"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-- The single FX1/Core source file allowed to import `Init.Prelude` directly. -/
def mayDirectlyImportFX1Prelude (sourceModuleName : Name) : Bool :=
  sourceModuleName == `LeanFX2.FX1.Core.Primitive

/-- The only host module one FX1 source file may import directly. -/
def isAllowedFX1PreludeImport
    (sourceModuleName importedModuleName : Name) :
    Bool :=
  mayDirectlyImportFX1Prelude sourceModuleName &&
    importedModuleName == `Init.Prelude

/-- Direct imports allowed from an FX1 module.

FX1/Core may only import FX1/Core.  FX1/LeanKernel may import FX1/Core and
FX1/LeanKernel.  Any future FX1 module outside those two namespaces must stay
inside `LeanFX2.FX1`.  The only allowed non-FX1 direct import is
`LeanFX2.FX1.Core.Primitive -> Init.Prelude`, matching the FX1/Core policy in
`kernel-sprint.md` §1.0.1 while keeping the host-prelude edge singular.
Host-heavy imports such as `Lean` or `Std` therefore fail at the source-import
boundary before dependency-closure audit even runs. -/
def isAllowedFX1DirectImport
    (sourceModuleName : Name) (importedModuleName : Name) :
    Bool :=
  if isAllowedFX1PreludeImport sourceModuleName importedModuleName then
    true
  else if isFX1CoreModuleName sourceModuleName then
    isFX1CoreModuleName importedModuleName
  else if isFX1LeanKernelModuleName sourceModuleName then
    isFX1CoreModuleName importedModuleName ||
      isFX1LeanKernelModuleName importedModuleName
  else
    isFX1ModuleName importedModuleName

/-- Forbidden direct imports for one FX1 module. -/
def forbiddenFX1ImportsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun forbiddenImports directImport =>
      if isAllowedFX1DirectImport sourceModuleName directImport.module then
        forbiddenImports
      else
        forbiddenImports.push directImport.module)

/-- Build-failing FX1 direct-import surface gate.  This complements
`#assert_fx1_core_host_minimal`: the host-minimal gate checks declaration
dependency closures, while this gate checks source-level module boundaries. -/
elab "#assert_fx1_import_surface_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedFX1Modules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isFX1ModuleName moduleName then
      scannedFX1Modules := scannedFX1Modules + 1
      let forbiddenImports := forbiddenFX1ImportsForModule moduleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (moduleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"FX1 import surface ok: {scannedFX1Modules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: forbidden direct imports [{renderedImports}]"
    let header :=
      s!"FX1 import surface FAILED: " ++
      s!"{violations.size} of {scannedFX1Modules} FX1 modules violate import policy"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## FX1 exact root-DAG import discipline -/

/-- Exact direct imports allowed for the current FX1/Core root DAG.

The broader `#assert_fx1_import_surface_clean` gate proves FX1 stays inside
the FX1 cone, apart from the single host-prelude edge.  This gate is stricter:
it pins the current minimal lambda-Pi root to the intended dependency DAG so a
leaf module cannot silently import the `Core` umbrella or a later metatheory
module.  When `Check` and `Soundness` land, this table must grow in the same
commit that adds those files. -/
def isAllowedFX1CoreExactDirectImport
    (sourceModuleName importedModuleName : Name) :
    Bool :=
  if sourceModuleName == `LeanFX2.FX1 then
    importedModuleName == `LeanFX2.FX1.Core ||
      importedModuleName == `LeanFX2.FX1.LeanKernel
  else if sourceModuleName == `LeanFX2.FX1.Core then
    importedModuleName == `LeanFX2.FX1.Core.Primitive ||
      importedModuleName == `LeanFX2.FX1.Core.Name ||
      importedModuleName == `LeanFX2.FX1.Core.Level ||
      importedModuleName == `LeanFX2.FX1.Core.Expr ||
      importedModuleName == `LeanFX2.FX1.Core.Declaration ||
      importedModuleName == `LeanFX2.FX1.Core.Environment ||
      importedModuleName == `LeanFX2.FX1.Core.Context ||
      importedModuleName == `LeanFX2.FX1.Core.Substitution ||
      importedModuleName == `LeanFX2.FX1.Core.Reduction ||
      importedModuleName == `LeanFX2.FX1.Core.HasType ||
      importedModuleName == `LeanFX2.FX1.Core.WellFormed ||
      importedModuleName == `LeanFX2.FX1.Core.Check ||
      importedModuleName == `LeanFX2.FX1.Core.Soundness
  else if sourceModuleName == `LeanFX2.FX1.Core.Primitive then
    importedModuleName == `Init.Prelude
  else if sourceModuleName == `LeanFX2.FX1.Core.Name then
    importedModuleName == `LeanFX2.FX1.Core.Primitive
  else if sourceModuleName == `LeanFX2.FX1.Core.Level then
    importedModuleName == `LeanFX2.FX1.Core.Name
  else if sourceModuleName == `LeanFX2.FX1.Core.Expr then
    importedModuleName == `LeanFX2.FX1.Core.Level
  else if sourceModuleName == `LeanFX2.FX1.Core.Declaration then
    importedModuleName == `LeanFX2.FX1.Core.Expr
  else if sourceModuleName == `LeanFX2.FX1.Core.Environment then
    importedModuleName == `LeanFX2.FX1.Core.Declaration
  else if sourceModuleName == `LeanFX2.FX1.Core.Context then
    importedModuleName == `LeanFX2.FX1.Core.Expr
  else if sourceModuleName == `LeanFX2.FX1.Core.Substitution then
    importedModuleName == `LeanFX2.FX1.Core.Expr
  else if sourceModuleName == `LeanFX2.FX1.Core.Reduction then
    importedModuleName == `LeanFX2.FX1.Core.Substitution
  else if sourceModuleName == `LeanFX2.FX1.Core.HasType then
    importedModuleName == `LeanFX2.FX1.Core.Environment ||
      importedModuleName == `LeanFX2.FX1.Core.Context ||
      importedModuleName == `LeanFX2.FX1.Core.Reduction
  else if sourceModuleName == `LeanFX2.FX1.Core.WellFormed then
    importedModuleName == `LeanFX2.FX1.Core.HasType
  else if sourceModuleName == `LeanFX2.FX1.Core.Check then
    importedModuleName == `LeanFX2.FX1.Core.HasType
  else if sourceModuleName == `LeanFX2.FX1.Core.Soundness then
    importedModuleName == `LeanFX2.FX1.Core.Check
  else
    false

/-- Direct imports that violate the exact FX1/Core root DAG. -/
def fx1CoreExactImportViolationsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun violations directImport =>
      if isAllowedFX1CoreExactDirectImport sourceModuleName directImport.module then
        violations
      else
        violations.push directImport.module)

/-- Build-failing gate for the exact FX1/Core root import DAG.

This checks only the current minimal root umbrella and `FX1/Core` modules.  It
does not police `FX1/LeanKernel` files; those are checked by
`#assert_fx1_lean_kernel_exact_import_shape`. -/
elab "#assert_fx1_core_exact_import_shape" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedRootModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if sourceModuleName == `LeanFX2.FX1 ||
        sourceModuleName == `LeanFX2.FX1.Core ||
        isFX1CoreModuleName sourceModuleName then
      scannedRootModules := scannedRootModules + 1
      let forbiddenImports :=
        fx1CoreExactImportViolationsForModule sourceModuleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (sourceModuleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"FX1/Core exact import shape ok: {scannedRootModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: unexpected direct imports [{renderedImports}]"
    let header :=
      s!"FX1/Core exact import shape FAILED: " ++
      s!"{violations.size} of {scannedRootModules} root modules violate the DAG"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## FX1/LeanKernel exact import discipline -/

/-- Exact direct imports allowed for the current FX1/LeanKernel DAG.

The Lean-kernel model is allowed to depend on FX1/Core through the broader FX1
source-import gate, but the current migrated scaffold does not need that edge
yet.  Keeping this table exact makes the first future dependency on FX1/Core
an explicit policy change in the same commit as the checker theorem work. -/
def isAllowedFX1LeanKernelExactDirectImport
    (sourceModuleName importedModuleName : Name) :
    Bool :=
  if sourceModuleName == `LeanFX2.FX1.LeanKernel then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Inductive ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.HasType ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.Check ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.Soundness ||
      importedModuleName == `LeanFX2.FX1.LeanKernel.Audit
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Name then
    importedModuleName == `LeanFX2.FX1.Core.Primitive
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Level then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Name
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Expr then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Level
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Substitution then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Expr
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Reduction then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Substitution
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Inductive then
    importedModuleName == `LeanFX2.FX1.LeanKernel.Reduction
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.HasType then
    false
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Check then
    false
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Soundness then
    false
  else if sourceModuleName == `LeanFX2.FX1.LeanKernel.Audit then
    false
  else
    false

/-- Direct imports that violate the exact FX1/LeanKernel DAG. -/
def fx1LeanKernelExactImportViolationsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun violations directImport =>
      if isAllowedFX1LeanKernelExactDirectImport
          sourceModuleName directImport.module then
        violations
      else
        violations.push directImport.module)

/-- Build-failing gate for the exact FX1/LeanKernel import DAG. -/
elab "#assert_fx1_lean_kernel_exact_import_shape" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLeanKernelModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if sourceModuleName == `LeanFX2.FX1.LeanKernel ||
        isFX1LeanKernelModuleName sourceModuleName then
      scannedLeanKernelModules := scannedLeanKernelModules + 1
      let forbiddenImports :=
        fx1LeanKernelExactImportViolationsForModule sourceModuleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (sourceModuleName, forbiddenImports)
  if violations.isEmpty then
    logInfo
      m!"FX1/LeanKernel exact import shape ok: {scannedLeanKernelModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: unexpected direct imports [{renderedImports}]"
    let header :=
      s!"FX1/LeanKernel exact import shape FAILED: " ++
      s!"{violations.size} of {scannedLeanKernelModules} modules violate the DAG"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## Legacy Lean-kernel scaffold isolation -/

/-- Modules allowed to import the legacy Lean-kernel scaffold directly. -/
def mayImportLegacyLeanKernelScaffold (sourceModuleName : Name) : Bool :=
  isLegacyLeanKernelScaffoldModuleName sourceModuleName ||
    (`LeanFX2.Tools).isPrefixOf sourceModuleName ||
    (`LeanFX2.Smoke).isPrefixOf sourceModuleName

/-- Legacy Lean-kernel direct imports that cross out of the allowed
audit/scaffold boundary. -/
def forbiddenLegacyLeanKernelImportsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun forbiddenImports directImport =>
      if isLegacyLeanKernelScaffoldModuleName directImport.module &&
          !mayImportLegacyLeanKernelScaffold sourceModuleName then
        forbiddenImports.push directImport.module
      else
        forbiddenImports)

/-- Build-failing isolation gate for old `LeanFX2.Lean.Kernel.*` modules.

This prevents rich production modules and the public `LeanFX2` umbrella from
depending on the old scaffold while Day 8 is retargeted to
`LeanFX2.FX1.LeanKernel`. -/
elab "#assert_legacy_lean_kernel_scaffold_isolated" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf moduleName then
      scannedModules := scannedModules + 1
      let forbiddenImports :=
        forbiddenLegacyLeanKernelImportsForModule moduleName moduleData
      if !forbiddenImports.isEmpty then
        violations := violations.push (moduleName, forbiddenImports)
  if violations.isEmpty then
    logInfo m!"legacy LeanKernel scaffold isolated: {scannedModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, forbiddenImports) =>
      let renderedImports :=
        String.intercalate ", " (forbiddenImports.toList.map toString)
      s!"  - {moduleName}: forbidden legacy LeanKernel imports [{renderedImports}]"
    let header :=
      s!"legacy LeanKernel scaffold isolation FAILED: " ++
      s!"{violations.size} of {scannedModules} modules import the old scaffold"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-- Direct project imports from one legacy Lean-kernel scaffold module that
escape the legacy scaffold namespace.  Non-project imports are ignored here
because Lean records the ambient `Init` prelude in module data; the global
host-heavy gate already catches broad host imports such as `Lean` or `Std`. -/
def legacyLeanKernelOutwardImportsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  if isLegacyLeanKernelScaffoldModuleName sourceModuleName then
    moduleData.imports.foldl
      (init := (#[] : Array Name))
      (fun outwardImports directImport =>
        if (`LeanFX2).isPrefixOf directImport.module &&
            !isLegacyLeanKernelScaffoldModuleName directImport.module then
          outwardImports.push directImport.module
        else
          outwardImports)
  else
    #[]

/-- Build-failing isolation gate for outbound dependencies of the old
`LeanFX2.Lean.Kernel.*` scaffold.

The legacy scaffold may depend on itself while it remains audited, but it must
not grow imports into the production kernel, FX1, tools, smoke tests, or the
public umbrella.  This keeps it quarantined while Day 8 moves toward
`LeanFX2.FX1.LeanKernel`. -/
elab "#assert_legacy_lean_kernel_import_surface_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLegacyModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isLegacyLeanKernelScaffoldModuleName moduleName then
      scannedLegacyModules := scannedLegacyModules + 1
      let outwardImports :=
        legacyLeanKernelOutwardImportsForModule moduleName moduleData
      if !outwardImports.isEmpty then
        violations := violations.push (moduleName, outwardImports)
  if violations.isEmpty then
    logInfo m!"legacy LeanKernel import surface ok: {scannedLegacyModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, outwardImports) =>
      let renderedImports :=
        String.intercalate ", " (outwardImports.toList.map toString)
      s!"  - {moduleName}: outward imports [{renderedImports}]"
    let header :=
      s!"legacy LeanKernel import surface FAILED: " ++
      s!"{violations.size} of {scannedLegacyModules} legacy modules import outside the scaffold"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## Production layer-import discipline -/

/-- Subject-reduction modules live under `Term/` for theorem naming, but
semantically depend on the reduction layer. -/
def isSubjectReductionMetatheoryModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Term.SubjectReduction ||
    moduleName == `LeanFX2.Term.SubjectReductionGeneral ||
    moduleName == `LeanFX2.Term.SubjectReductionUniverse

/-- Reduction modules that are metatheorems about conversion or canonical
forms, not primitive reduction infrastructure. -/
def isReductionMetatheoryModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Reduction.ConvCanonical ||
    moduleName == `LeanFX2.Reduction.ConvCongIsClosedTy

/-- Cross-theory bridge modules depend on HoTT, Cubical, or Modal layers and
therefore must not be classified with the low-level typed/raw bridge. -/
def isCrossTheoryBridgeModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2.Cubical.Bridge ||
    moduleName == `LeanFX2.Cubical.Ua ||
    moduleName == `LeanFX2.Bridge.PathToId ||
    moduleName == `LeanFX2.Bridge.IdToPath ||
    moduleName == `LeanFX2.Bridge.PathIdInverse ||
    moduleName == `LeanFX2.Bridge.PathIdMeta ||
    moduleName == `LeanFX2.Bridge.IdEqType ||
    moduleName == `LeanFX2.Bridge.PathEqType ||
    moduleName == `LeanFX2.Bridge.BoxObservational ||
    moduleName == `LeanFX2.Bridge.BoxCubical

/-- Semantic import layer for production modules.  The numbering matches the
public `LeanFX2.lean` umbrella comments after refining path names that carry
metatheory (`Term.SubjectReduction*`) or cross-theory bridge content.

`none` means the module is outside this production layering contract and is
checked by a different gate (`FX1`, tooling, smoke, sketches, or legacy
LeanKernel). -/
def productionImportLayer? (moduleName : Name) : Option Nat :=
  if moduleName == `LeanFX2.Kernel then
    some 4
  else if moduleName == `LeanFX2.Rich then
    some 13
  else if isSubjectReductionMetatheoryModuleName moduleName then
    some 3
  else if isReductionMetatheoryModuleName moduleName then
    some 3
  else if isCrossTheoryBridgeModuleName moduleName then
    some 13
  else if (`LeanFX2.Foundation).isPrefixOf moduleName then
    some 0
  else if moduleName == `LeanFX2.Term ||
      (`LeanFX2.Term).isPrefixOf moduleName then
    some 1
  else if (`LeanFX2.Reduction).isPrefixOf moduleName then
    some 2
  else if moduleName == `LeanFX2.Bridge then
    some 3
  else if (`LeanFX2.Confluence).isPrefixOf moduleName then
    some 4
  else if (`LeanFX2.HoTT).isPrefixOf moduleName ||
      (`LeanFX2.Cubical).isPrefixOf moduleName then
    some 5
  else if (`LeanFX2.Modal).isPrefixOf moduleName then
    some 6
  else if (`LeanFX2.Effects).isPrefixOf moduleName ||
      (`LeanFX2.Sessions).isPrefixOf moduleName ||
      (`LeanFX2.Codata).isPrefixOf moduleName then
    some 7
  else if (`LeanFX2.Graded).isPrefixOf moduleName then
    some 8
  else if (`LeanFX2.Refine).isPrefixOf moduleName then
    some 9
  else if (`LeanFX2.Algo).isPrefixOf moduleName then
    some 10
  else if (`LeanFX2.Surface).isPrefixOf moduleName then
    some 11
  else if moduleName == `LeanFX2.Pipeline then
    some 12
  else if (`LeanFX2.Conservativity).isPrefixOf moduleName ||
      (`LeanFX2.Translation).isPrefixOf moduleName ||
      (`LeanFX2.InternalLanguage).isPrefixOf moduleName then
    some 13
  else
    none

/-- Does a direct import point from a lower semantic layer to a higher one? -/
def isLayerImportViolation
    (sourceModuleName importedModuleName : Name) : Bool :=
  match productionImportLayer? sourceModuleName,
      productionImportLayer? importedModuleName with
  | some sourceLayer, some importedLayer => sourceLayer < importedLayer
  | _, _ => false

/-- Direct upward imports for one production module. -/
def layerImportViolationsForModule
    (sourceModuleName : Name) (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun violations directImport =>
      if isLayerImportViolation sourceModuleName directImport.module then
        violations.push directImport.module
      else
        violations)

/-- Build-failing gate for semantic production layering.  This complements
the broad import-surface gates: it does not care whether an import is host or
tooling, but whether a production module imports a later production layer. -/
elab "#assert_production_layer_imports_clean" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLayeredModules : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if moduleName != `LeanFX2 &&
        isProductionLeanFX2ModuleName moduleName &&
        (productionImportLayer? moduleName).isSome then
      scannedLayeredModules := scannedLayeredModules + 1
      let upwardImports := layerImportViolationsForModule moduleName moduleData
      if !upwardImports.isEmpty then
        violations := violations.push (moduleName, upwardImports)
  if violations.isEmpty then
    logInfo m!"production layer imports ok: {scannedLayeredModules} modules"
  else
    let perModuleLines := violations.toList.map fun (moduleName, upwardImports) =>
      let renderedImports :=
        String.intercalate ", " (upwardImports.toList.map toString)
      s!"  - {moduleName}: upward imports [{renderedImports}]"
    let header :=
      s!"production layer imports FAILED: " ++
      s!"{violations.size} of {scannedLayeredModules} modules import later layers"
    throwError (header ++ "\n" ++ String.intercalate "\n" perModuleLines)

/-! ## Redundant direct project-import discipline -/

/-- Convert the loaded module header into the compact lookup shape used by
import-reachability checks. -/
def loadedModuleImportEntries (environment : Environment) :
    Array (Name × ModuleData) :=
  (Array.zip environment.header.modules environment.header.moduleData).map
    (fun (effectiveImport, moduleData) => (effectiveImport.module, moduleData))

/-- Direct imports recorded for one source module in the currently loaded
module graph. -/
def directImportNamesForModuleName
    (moduleEntries : Array (Name × ModuleData))
    (sourceModuleName : Name) :
    List Name :=
  match moduleEntries.find? (fun (entryName, _) => entryName == sourceModuleName) with
  | some (_, moduleData) =>
      moduleData.imports.toList.map (fun directImport => directImport.module)
  | none => []

/-- Fuel-bounded reachability over direct module imports.

The fuel is normally the number of loaded modules plus one.  A visited list
prevents cycles from expanding forever; the fuel keeps the definition plainly
structural and acceptable to the kernel. -/
def isModuleReachableFromFrontierWithFuel
    (moduleEntries : Array (Name × ModuleData))
    (targetModuleName : Name)
    (fuel : Nat)
    (visitedModuleNames : List Name)
    (frontierModuleNames : List Name) :
    Bool :=
  match fuel with
  | 0 => false
  | Nat.succ remainingFuel =>
      match frontierModuleNames with
      | [] => false
      | candidateModuleName :: remainingFrontier =>
          if candidateModuleName == targetModuleName then
            true
          else if visitedModuleNames.contains candidateModuleName then
            isModuleReachableFromFrontierWithFuel
              moduleEntries targetModuleName remainingFuel visitedModuleNames
              remainingFrontier
          else
            let candidateImports :=
              directImportNamesForModuleName moduleEntries candidateModuleName
            isModuleReachableFromFrontierWithFuel
              moduleEntries targetModuleName remainingFuel
              (candidateModuleName :: visitedModuleNames)
              (candidateImports ++ remainingFrontier)

/-- Project-local direct imports from one module.  Host imports are handled by
the host-heavy gates and by FX1's stricter prelude rule. -/
def directProjectImportNamesForModuleData
    (moduleData : ModuleData) :
    Array Name :=
  moduleData.imports.foldl
    (init := (#[] : Array Name))
    (fun projectImports directImport =>
      if (`LeanFX2).isPrefixOf directImport.module then
        projectImports.push directImport.module
      else
        projectImports)

/-- Public entrypoints are intentionally broad and are checked by umbrella
isolation/reachability gates rather than by redundant-edge minimization. -/
def shouldScanRedundantProjectImportsForModule
    (sourceModuleName : Name) :
    Bool :=
  isProductionLeanFX2ModuleName sourceModuleName &&
    !isPublicUmbrellaImportModuleName sourceModuleName

/-- Documented direct imports that are intentionally kept even though the
target is reachable through another loaded project import.

These four edges name semantic dependencies that are core to the source
module's interface, not incidental transitive conveniences.  Keeping the
allowlist small makes future redundancy drift fail fast. -/
def isDocumentedRedundantProjectImport
    (sourceModuleName importedModuleName : Name) :
    Bool :=
  (sourceModuleName == `LeanFX2.Term &&
      importedModuleName == `LeanFX2.Foundation.RawTerm) ||
    (sourceModuleName == `LeanFX2.Term &&
      importedModuleName == `LeanFX2.Foundation.Ty) ||
    (sourceModuleName == `LeanFX2.Graded.Rules &&
      importedModuleName == `LeanFX2.Graded.GradeVector) ||
    (sourceModuleName == `LeanFX2.Graded.Dimensions21 &&
      importedModuleName == `LeanFX2.Graded.Instances.Complexity)

/-- Redundant direct imports for one production module.  A direct import is
redundant when the same project module is reachable through the source's other
direct imports. -/
def redundantProjectImportsForModule
    (moduleEntries : Array (Name × ModuleData))
    (sourceModuleName : Name)
    (moduleData : ModuleData) :
    Array DirectImportRecord :=
  let directProjectImports := directProjectImportNamesForModuleData moduleData
  directProjectImports.foldl
    (init := (#[] : Array DirectImportRecord))
    (fun redundantImports importedModuleName =>
      if isDocumentedRedundantProjectImport sourceModuleName importedModuleName then
        redundantImports
      else
        let otherDirectImports :=
          directProjectImports.toList.filter
            (fun candidateModuleName => candidateModuleName != importedModuleName)
        let isReachableWithoutDirectEdge :=
          isModuleReachableFromFrontierWithFuel moduleEntries importedModuleName
            (moduleEntries.size + 1) [] otherDirectImports
        if isReachableWithoutDirectEdge then
          redundantImports.push {
            sourceModuleName := sourceModuleName
            importedModuleName := importedModuleName
          }
        else
          redundantImports)

/-- Build-failing gate for redundant direct project imports in production
modules.

This turns the repository import-pruning script into a durable invariant:
regular production modules should import the narrow modules they actually use,
but not keep extra direct project edges that are already supplied by another
direct import. -/
elab "#assert_no_redundant_production_project_imports" : command => do
  let environment ← getEnv
  let moduleEntries := loadedModuleImportEntries environment
  let mut scannedProductionModules : Nat := 0
  let mut violations : Array DirectImportRecord := #[]
  for (sourceModuleName, moduleData) in moduleEntries do
    if shouldScanRedundantProjectImportsForModule sourceModuleName then
      scannedProductionModules := scannedProductionModules + 1
      violations :=
        violations ++
          redundantProjectImportsForModule
            moduleEntries sourceModuleName moduleData
  if violations.isEmpty then
    logInfo
      m!"redundant production project imports ok: {scannedProductionModules} modules"
  else
    let renderedImports := formatDirectImportRecords violations
    let header :=
      s!"redundant production project imports FAILED: " ++
      s!"{violations.size} redundant direct project imports"
    throwError (header ++ "\n  " ++ renderedImports)

/-! ## Import-surface summary

The fail-fast gates above catch invalid dependency edges.  This
summary is intentionally informational: it keeps the current import
cone visible in every import-surface smoke run, including the few
allowed host/tooling edges that should remain explicit rather than
hidden in prose.
-/

/-- Does this direct import point from a project module to a host-heavy
module that should stay rare and visible? -/
def isHostHeavyDirectImportModuleName (moduleName : Name) : Bool :=
  (`Lean).isPrefixOf moduleName ||
    (`Lake).isPrefixOf moduleName ||
    (`Std).isPrefixOf moduleName ||
    (`Mathlib).isPrefixOf moduleName ||
    (`Classical).isPrefixOf moduleName ||
    (`Quot).isPrefixOf moduleName

/-- Explicit allowlist for direct host-heavy imports anywhere inside
`LeanFX2.*`.

Only the audit implementation itself may import Lean elaborator APIs.  FX1's
temporary `Init.Prelude` imports are intentionally not host-heavy here: the
FX1-specific source and declaration gates police them separately. -/
def isAllowedHostHeavyDirectImport
    (directImportRecord : DirectImportRecord) :
    Bool :=
  directImportRecord.sourceModuleName == `LeanFX2.Tools.DependencyAudit &&
    directImportRecord.importedModuleName == `Lean

/-! ## Public umbrella reachability -/

/-- Whether a module is one of the public roots that should reach all
production modules.  `LeanFX2` intentionally does not import FX1 directly,
so the reachability root set has two entries. -/
def isPublicProductionRootModuleName (moduleName : Name) : Bool :=
  moduleName == `LeanFX2 || moduleName == `LeanFX2.FX1

/-- Is a project module already present in a small name set? -/
def containsModuleName (moduleNames : Array Name) (moduleName : Name) :
    Bool :=
  moduleNames.contains moduleName

/-- Build-failing gate that checks every loaded production module is reachable
from the public production roots `LeanFX2` or `LeanFX2.FX1`.

This is intentionally run from `Smoke.ImportEverywhere`, where Lake has loaded
the whole library glob.  Running it only from `Smoke.ImportSurface` would see
only the already-public cone and could not detect a production module that is
loaded only by a smoke audit. -/
elab "#assert_public_production_umbrella_reaches_all" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut reachableModuleNames : Array Name := #[`LeanFX2, `LeanFX2.FX1]
  for _iteration in List.range moduleEntries.size do
    for (effectiveImport, moduleData) in moduleEntries do
      let sourceModuleName := effectiveImport.module
      if containsModuleName reachableModuleNames sourceModuleName then
        for directImport in moduleData.imports do
          let importedModuleName := directImport.module
          if (`LeanFX2).isPrefixOf importedModuleName &&
              !containsModuleName reachableModuleNames importedModuleName then
            reachableModuleNames := reachableModuleNames.push importedModuleName
  let mut missingProductionModules : Array Name := #[]
  let mut scannedProductionModules : Nat := 0
  for (effectiveImport, _moduleData) in moduleEntries do
    let moduleName := effectiveImport.module
    if isProductionLeanFX2ModuleName moduleName then
      scannedProductionModules := scannedProductionModules + 1
      if !containsModuleName reachableModuleNames moduleName then
        missingProductionModules := missingProductionModules.push moduleName
  if missingProductionModules.isEmpty then
    logInfo
      m!"public production umbrella reachability ok: {scannedProductionModules} modules"
  else
    let renderedModules :=
      String.intercalate ", " (missingProductionModules.toList.map toString)
    let header :=
      s!"public production umbrella reachability FAILED: " ++
      s!"{missingProductionModules.size} of {scannedProductionModules} " ++
      "production modules are not reachable from LeanFX2 or LeanFX2.FX1"
    throwError (header ++ "\n  " ++ renderedModules)

/-- Coarse family label for import-census summaries.  The label is
informational only; policy gates above enforce the actual boundaries. -/
def importFamilyLabel (moduleName : Name) : String :=
  if moduleName == `LeanFX2 then
    "LeanFX2.Root"
  else if moduleName == `LeanFX2.Kernel then
    "LeanFX2.Kernel"
  else if moduleName == `LeanFX2.Rich then
    "LeanFX2.Rich"
  else if (`LeanFX2.FX1).isPrefixOf moduleName then
    "LeanFX2.FX1"
  else if isLegacyLeanKernelScaffoldModuleName moduleName then
    "LeanFX2.LegacyLeanKernel"
  else if isHostBoundaryModuleName moduleName then
    "LeanFX2.HostBoundary"
  else if (`LeanFX2.Tools).isPrefixOf moduleName then
    "LeanFX2.Tools"
  else if (`LeanFX2.Smoke).isPrefixOf moduleName then
    "LeanFX2.Smoke"
  else if (`LeanFX2.Sketch).isPrefixOf moduleName then
    "LeanFX2.Sketch"
  else if (`LeanFX2.Foundation).isPrefixOf moduleName then
    "LeanFX2.Foundation"
  else if moduleName == `LeanFX2.Term ||
      (`LeanFX2.Term).isPrefixOf moduleName then
    "LeanFX2.Term"
  else if (`LeanFX2.Reduction).isPrefixOf moduleName then
    "LeanFX2.Reduction"
  else if moduleName == `LeanFX2.Bridge ||
      (`LeanFX2.Bridge).isPrefixOf moduleName then
    "LeanFX2.Bridge"
  else if (`LeanFX2.Confluence).isPrefixOf moduleName then
    "LeanFX2.Confluence"
  else if (`LeanFX2.HoTT).isPrefixOf moduleName then
    "LeanFX2.HoTT"
  else if (`LeanFX2.Cubical).isPrefixOf moduleName then
    "LeanFX2.Cubical"
  else if (`LeanFX2.Modal).isPrefixOf moduleName then
    "LeanFX2.Modal"
  else if (`LeanFX2.Effects).isPrefixOf moduleName then
    "LeanFX2.Effects"
  else if (`LeanFX2.Sessions).isPrefixOf moduleName then
    "LeanFX2.Sessions"
  else if (`LeanFX2.Codata).isPrefixOf moduleName then
    "LeanFX2.Codata"
  else if (`LeanFX2.Graded).isPrefixOf moduleName then
    "LeanFX2.Graded"
  else if (`LeanFX2.Refine).isPrefixOf moduleName then
    "LeanFX2.Refine"
  else if (`LeanFX2.Algo).isPrefixOf moduleName then
    "LeanFX2.Algo"
  else if (`LeanFX2.Surface).isPrefixOf moduleName then
    "LeanFX2.Surface"
  else if moduleName == `LeanFX2.Pipeline then
    "LeanFX2.Pipeline"
  else if (`LeanFX2.Conservativity).isPrefixOf moduleName then
    "LeanFX2.Conservativity"
  else if (`LeanFX2.Translation).isPrefixOf moduleName then
    "LeanFX2.Translation"
  else if (`LeanFX2.InternalLanguage).isPrefixOf moduleName then
    "LeanFX2.InternalLanguage"
  else if (`Lean).isPrefixOf moduleName then
    "Host.Lean"
  else if (`Lake).isPrefixOf moduleName then
    "Host.Lake"
  else if (`Std).isPrefixOf moduleName then
    "Host.Std"
  else if (`Init).isPrefixOf moduleName then
    "Host.Init"
  else if (`Classical).isPrefixOf moduleName then
    "Host.Classical"
  else if (`Quot).isPrefixOf moduleName then
    "Host.Quot"
  else
    "Other"

/-- Increment an import-family count in a small association list. -/
def incrementImportFamilyCount
    (counts : Array (String × Nat)) (familyLabel : String) :
    Array (String × Nat) :=
  match counts.findIdx? (fun (storedLabel, _) => storedLabel == familyLabel) with
  | some familyIndex =>
      counts.modify familyIndex
        (fun (storedLabel, count) => (storedLabel, count + 1))
  | none => counts.push (familyLabel, 1)

/-- Render import-family counts in stable first-seen order. -/
def formatImportFamilyCounts (counts : Array (String × Nat)) : String :=
  if counts.isEmpty then
    "none"
  else
    String.intercalate "; "
      (counts.toList.map fun (familyLabel, count) =>
        s!"{familyLabel}={count}")

/-- Build-failing global host-heavy import gate.

This scans every loaded `LeanFX2.*` module, including tools and smoke tests.
The broader production gates already forbid host-heavy imports in production
modules; this gate also keeps tools/smoke host imports explicit and prevents a
second accidental `import Lean` from entering unnoticed. -/
elab "#assert_host_heavy_import_surface_allowlisted" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut scannedLeanFX2Modules : Nat := 0
  let mut violations : Array DirectImportRecord := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf sourceModuleName then
      scannedLeanFX2Modules := scannedLeanFX2Modules + 1
      for directImport in moduleData.imports do
        let directImportRecord : DirectImportRecord := {
          sourceModuleName := sourceModuleName
          importedModuleName := directImport.module
        }
        if isHostHeavyDirectImportModuleName directImport.module &&
            !isAllowedHostHeavyDirectImport directImportRecord then
          violations := violations.push directImportRecord
  if violations.isEmpty then
    logInfo m!"host-heavy import allowlist ok: {scannedLeanFX2Modules} modules"
  else
    let renderedImports := formatDirectImportRecords violations
    let header :=
      s!"host-heavy import allowlist FAILED: " ++
      s!"{violations.size} forbidden direct host-heavy imports"
    throwError (header ++ "\n  " ++ renderedImports)

/-- Informational import-family census over the currently loaded
`LeanFX2.*` modules.  This exposes import mass by source family and target
family without creating a committed report file. -/
elab "#audit_import_family_summary" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut sourceFamilyCounts : Array (String × Nat) := #[]
  let mut targetFamilyCounts : Array (String × Nat) := #[]
  let mut directImportCount : Nat := 0
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf sourceModuleName then
      sourceFamilyCounts :=
        incrementImportFamilyCount sourceFamilyCounts
          (importFamilyLabel sourceModuleName)
      for directImport in moduleData.imports do
        directImportCount := directImportCount + 1
        targetFamilyCounts :=
          incrementImportFamilyCount targetFamilyCounts
            (importFamilyLabel directImport.module)
  logInfo
    (String.intercalate "\n" [
      "──────────── IMPORT FAMILY SUMMARY ────────────",
      s!"  Direct import edges scanned: {directImportCount}",
      s!"  Source families: {formatImportFamilyCounts sourceFamilyCounts}",
      s!"  Target families: {formatImportFamilyCounts targetFamilyCounts}",
      "───────────────────────────────────────────────"
    ])

/-- Informational import summary over the currently loaded `LeanFX2.*`
modules.  This is not a policy gate; the policy gates above remain the
build-failing checks. -/
elab "#audit_import_surface_summary" : command => do
  let environment ← getEnv
  let moduleEntries :=
    Array.zip environment.header.modules environment.header.moduleData
  let mut leanFX2ModuleCount : Nat := 0
  let mut productionModuleCount : Nat := 0
  let mut richProductionModuleCount : Nat := 0
  let mut fx1ModuleCount : Nat := 0
  let mut toolsModuleCount : Nat := 0
  let mut smokeModuleCount : Nat := 0
  let mut sketchModuleCount : Nat := 0
  let mut legacyLeanKernelModuleCount : Nat := 0
  let mut publicUmbrellaHeaderImportCount : Nat := 0
  let mut directImportCount : Nat := 0
  let mut hostHeavyDirectImports : Array DirectImportRecord := #[]
  let mut richProductionFX1Imports : Array DirectImportRecord := #[]
  let mut richProductionHostImports : Array DirectImportRecord := #[]
  let mut legacyLeanKernelImports : Array DirectImportRecord := #[]
  let mut legacyLeanKernelOutwardImports : Array DirectImportRecord := #[]
  let mut hostBoundaryImports : Array DirectImportRecord := #[]
  let mut fx1ForbiddenImports : Array DirectImportRecord := #[]
  let mut fx1PreludeImports : Array DirectImportRecord := #[]
  for (effectiveImport, moduleData) in moduleEntries do
    let sourceModuleName := effectiveImport.module
    if (`LeanFX2).isPrefixOf sourceModuleName then
      leanFX2ModuleCount := leanFX2ModuleCount + 1
      if isProductionLeanFX2ModuleName sourceModuleName then
        productionModuleCount := productionModuleCount + 1
      if isRichProductionLeanFX2ModuleName sourceModuleName then
        richProductionModuleCount := richProductionModuleCount + 1
      if isFX1ModuleName sourceModuleName then
        fx1ModuleCount := fx1ModuleCount + 1
      if (`LeanFX2.Tools).isPrefixOf sourceModuleName then
        toolsModuleCount := toolsModuleCount + 1
      if (`LeanFX2.Smoke).isPrefixOf sourceModuleName then
        smokeModuleCount := smokeModuleCount + 1
      if (`LeanFX2.Sketch).isPrefixOf sourceModuleName then
        sketchModuleCount := sketchModuleCount + 1
      if isLegacyLeanKernelScaffoldModuleName sourceModuleName then
        legacyLeanKernelModuleCount := legacyLeanKernelModuleCount + 1
      for directImport in moduleData.imports do
        let importedModuleName := directImport.module
        if sourceModuleName == `LeanFX2 then
          publicUmbrellaHeaderImportCount := publicUmbrellaHeaderImportCount + 1
        directImportCount := directImportCount + 1
        let directImportRecord : DirectImportRecord := {
          sourceModuleName := sourceModuleName
          importedModuleName := importedModuleName
        }
        if isHostHeavyDirectImportModuleName importedModuleName then
          hostHeavyDirectImports :=
            hostHeavyDirectImports.push directImportRecord
        if isRichProductionLeanFX2ModuleName sourceModuleName &&
            isFX1ModuleName importedModuleName then
          richProductionFX1Imports :=
            richProductionFX1Imports.push directImportRecord
        if isRichProductionLeanFX2ModuleName sourceModuleName &&
            isHostHeavyDirectImportModuleName importedModuleName then
          richProductionHostImports :=
            richProductionHostImports.push directImportRecord
        if isLegacyLeanKernelScaffoldModuleName importedModuleName then
          legacyLeanKernelImports :=
            legacyLeanKernelImports.push directImportRecord
        if isLegacyLeanKernelScaffoldModuleName sourceModuleName &&
            (`LeanFX2).isPrefixOf importedModuleName &&
            !isLegacyLeanKernelScaffoldModuleName importedModuleName then
          legacyLeanKernelOutwardImports :=
            legacyLeanKernelOutwardImports.push directImportRecord
        if isHostBoundaryModuleName importedModuleName then
          hostBoundaryImports :=
            hostBoundaryImports.push directImportRecord
        if isFX1ModuleName sourceModuleName &&
            !isAllowedFX1DirectImport sourceModuleName importedModuleName then
          fx1ForbiddenImports :=
            fx1ForbiddenImports.push directImportRecord
        if isFX1ModuleName sourceModuleName &&
            importedModuleName == `Init.Prelude then
          fx1PreludeImports :=
            fx1PreludeImports.push directImportRecord
  logInfo
    (String.intercalate "\n" [
      "──────────── IMPORT SURFACE SUMMARY ────────────",
      s!"  LeanFX2 modules visible:          {leanFX2ModuleCount}",
      s!"  Production modules:               {productionModuleCount}",
      s!"  Rich production modules:          {richProductionModuleCount}",
      s!"  FX1 modules:                      {fx1ModuleCount}",
      s!"  Tool modules:                     {toolsModuleCount}",
      s!"  Smoke modules:                    {smokeModuleCount}",
      s!"  Sketch modules:                   {sketchModuleCount}",
      s!"  Legacy LeanKernel modules:        {legacyLeanKernelModuleCount}",
      s!"  Public umbrella header imports:   {publicUmbrellaHeaderImportCount}",
      s!"  Direct import edges scanned:      {directImportCount}",
      s!"  Host-heavy direct imports:        {hostHeavyDirectImports.size}",
      s!"    {formatDirectImportRecords hostHeavyDirectImports}",
      s!"  Rich-production -> FX1 imports:   {richProductionFX1Imports.size}",
      s!"    {formatDirectImportRecords richProductionFX1Imports}",
      s!"  Rich-production host imports:     {richProductionHostImports.size}",
      s!"    {formatDirectImportRecords richProductionHostImports}",
      s!"  Legacy LeanKernel direct imports: {legacyLeanKernelImports.size}",
      s!"    {formatDirectImportRecords legacyLeanKernelImports}",
      s!"  Legacy LeanKernel outward imports: {legacyLeanKernelOutwardImports.size}",
      s!"    {formatDirectImportRecords legacyLeanKernelOutwardImports}",
      s!"  Host-boundary direct imports:   {hostBoundaryImports.size}",
      s!"    {formatDirectImportRecords hostBoundaryImports}",
      s!"  FX1 forbidden direct imports:     {fx1ForbiddenImports.size}",
      s!"    {formatDirectImportRecords fx1ForbiddenImports}",
      s!"  FX1 direct Init.Prelude imports:  {fx1PreludeImports.size}",
      s!"    {formatDirectImportRecords fx1PreludeImports}",
      "────────────────────────────────────────────────"
    ])

/-! ## Raw/typed parity check -/

/-- Get the constructor names of an inductive type. -/
def getInductiveConstructorNames
    (environment : Environment) (inductiveName : Name) :
    Array Name :=
  match environment.find? inductiveName with
  | some (.inductInfo inductiveInfo) => inductiveInfo.ctors.toArray
  | _ => #[]

/-- Strip a namespace prefix off a name and return just the final
component as a string.  Used for matching raw / typed ctor suffixes. -/
def Name.lastSegmentString (someName : Name) : String :=
  match someName with
  | .anonymous => ""
  | .str _ part => part
  | .num _ index => toString index

/-- Documented raw-only constructors that intentionally have no typed
counterpart in the current snapshot.  The remaining entries are
structural raw rules whose typed layer intentionally represents the same
operation through a different constructor family.  Tracking them as
documented exceptions means the parity gate still catches NEW raw-only
ctors going forward, while the remaining gaps are recorded explicitly
rather than being silently allowed.

Discipline for moving an entry OUT of this list: add the matching
`Step.par.X` constructor in `Reduction/ParRed.lean`, mirror the
`Confluence/RawCd.lean` and `Confluence/RawCdLemma.lean` entries to
`Confluence/Cd.lean` and `Confluence/CdLemma.lean`, then delete the
entry below. -/
def isDocumentedRawOnlyParity (rawCtorName : Name) : Bool :=
  let suffix := Name.lastSegmentString rawCtorName
  -- Section A: parametric type-code cong rules (CUMUL-2 cumulativity
  -- type-codes ship raw-only; typed cumulativity uses cumulUp directly).
  suffix == "arrowCodeCong" ||
  suffix == "piTyCodeCong" ||
  suffix == "sigmaTyCodeCong" ||
  suffix == "productCodeCong" ||
  suffix == "sumCodeCong" ||
  suffix == "listCodeCong" ||
  suffix == "optionCodeCong" ||
  suffix == "eitherCodeCong" ||
  suffix == "idCodeCong" ||
  suffix == "equivCodeCong" ||
  suffix == "cumulUpMarkerCong" ||
  -- Section B: refl cong rule (typed Term.refl uses different reduction
  -- shape; raw reflCong is structural-only).
  suffix == "reflCong"

/-- Build-failing parity gate.  For every constructor of
`LeanFX2.RawStep.par` whose suffix is not in the documented raw-only
list, the constructor with the same suffix must exist in
`LeanFX2.Step.par`. -/
elab "#assert_raw_typed_parity" : command => do
  let environment ← getEnv
  let rawCtors := getInductiveConstructorNames environment `LeanFX2.RawStep.par
  let typedCtors := getInductiveConstructorNames environment `LeanFX2.Step.par
  let typedSuffixes : Std.HashSet String :=
    typedCtors.foldl (init := {}) fun acc ctorName =>
      acc.insert (Name.lastSegmentString ctorName)
  let mut missing : Array Name := #[]
  for rawCtorName in rawCtors do
    let suffix := Name.lastSegmentString rawCtorName
    if !typedSuffixes.contains suffix && !isDocumentedRawOnlyParity rawCtorName then
      missing := missing.push rawCtorName
  if missing.isEmpty then
    logInfo s!"raw/typed parity ok: {rawCtors.size} raw ctors have typed mirror ({typedCtors.size} typed ctors)"
  else
    let perCtorLines := missing.toList.map fun rawCtorName =>
      s!"  - {rawCtorName} -> expected LeanFX2.Step.par.{Name.lastSegmentString rawCtorName} (missing)"
    let header :=
      s!"raw/typed parity FAILED: {missing.size} raw ctors lack typed counterpart"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-! ## End-of-build summary reporter -/

/-- Aggregate audit summary across one namespace.  Logs total / clean /
failed counts.  Does NOT throw — strictly informational, for human
visibility amid build noise.  Used at the end of `Tools/AuditAll.lean`
to surface the overall audit health regardless of which gate fired. -/
elab "#audit_summary " namespaceSyntax:ident : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut totalCount : Nat := 0
  let mut cleanCount : Nat := 0
  let mut failedDecls : Array (Name × Array StrictViolation) := #[]
  for targetName in targetNames do
    totalCount := totalCount + 1
    match environment.find? targetName with
    | none => continue
    | some constantInfo =>
        let violations := classifyStrictViolations environment targetName constantInfo
        if violations.isEmpty then
          cleanCount := cleanCount + 1
        else
          failedDecls := failedDecls.push (targetName, violations)
  let summaryHeader :=
    "════════════════ STRICT AUDIT SUMMARY ════════════════"
  let summaryLines : List String := [
    summaryHeader,
    s!"  Namespace:        {namespaceName}",
    s!"  Total audited:    {totalCount}",
    s!"  Clean (passed):   {cleanCount}",
    s!"  Failed:           {failedDecls.size}"
  ]
  let allLines :=
    if failedDecls.isEmpty then
      summaryLines ++
        ["═══════════════════════════════════════════════════════"]
    else
      let perDeclLines :=
        failedDecls.toList.map fun (someName, violations) =>
          s!"    ✗ {someName}: {formatViolationList violations}"
      summaryLines ++
        ["  Failures:"] ++ perDeclLines ++
        ["═══════════════════════════════════════════════════════"]
  logInfo (String.intercalate "\n" allLines)

/-! ## Naming discipline gate

CLAUDE.md mandates ASCII-only identifiers ≥ 4 characters with
question-verb predicates.  This gate enforces the first two rules
mechanically.  The third (question-verb predicates for booleans) is
heuristic and not yet checked. -/

/-- Whitelist of canonical short identifiers permitted by the spec.
Per CLAUDE.md "Allowed exceptions": kernel translation primitives,
parser terminology, and standard math conventions. -/
def isWhitelistedShortIdentifier (someSegment : String) : Bool :=
  -- Spec primitives (CLAUDE.md §31 Kernel Translation)
  someSegment == "shift" ||
  someSegment == "subst" ||
  someSegment == "whnf" ||
  someSegment == "convEq" ||
  someSegment == "beta" ||
  someSegment == "eta" ||
  someSegment == "iota" ||
  someSegment == "refl" ||
  someSegment == "cd" ||
  -- Parser terminology
  someSegment == "lhs" ||
  someSegment == "rhs" ||
  -- Common math + Lean conventions
  someSegment == "Nat" ||
  someSegment == "Fin" ||
  someSegment == "Bool" ||
  someSegment == "Unit" ||
  someSegment == "Prop" ||
  someSegment == "Type" ||
  someSegment == "Sort" ||
  -- FX project core types kept short for readability across thousands
  -- of usages (Term, RawTerm, Ty, Mode, Step, Conv).  Each is the
  -- canonical name for a fundamental kernel concept; renaming would
  -- harm readability more than discipline gains.
  someSegment == "Term" ||
  someSegment == "Ty" ||
  someSegment == "Ctx" ||
  someSegment == "Mode" ||
  someSegment == "Step" ||
  someSegment == "Conv" ||
  -- Common short fragments shipped before naming discipline tightened;
  -- listed explicitly so the gate accepts them while flagging genuinely
  -- new short names.
  someSegment == "id" ||
  someSegment == "le" ||
  someSegment == "or" ||
  someSegment == "of" ||
  someSegment == "to" ||
  someSegment == "is" ||
  someSegment == "as" ||
  someSegment == "in" ||
  someSegment == "fn" ||
  someSegment == "rec" ||
  someSegment == "act" ||
  someSegment == "lam" ||
  someSegment == "app" ||
  someSegment == "fst" ||
  someSegment == "snd" ||
  someSegment == "zip" ||
  someSegment == "max" ||
  someSegment == "min" ||
  someSegment == "add" ||
  someSegment == "mul" ||
  someSegment == "rfl" ||
  someSegment == "var" ||
  someSegment == "set" ||
  someSegment == "get" ||
  someSegment == "rev" ||
  someSegment == "map" ||
  someSegment == "ite" ||
  someSegment == "abs" ||
  -- Parser and surface-standard-library vocabulary.  These are
  -- canonical spellings of FX tokens or target names, not throwaway
  -- abbreviations.
  someSegment == "sub" ||
  someSegment == "neg" ||
  someSegment == "lt" ||
  someSegment == "gt" ||
  someSegment == "ge" ||
  someSegment == "ne" ||
  someSegment == "shl" ||
  someSegment == "shr" ||
  someSegment == "eof" ||
  someSegment == "all" ||
  someSegment == "std" ||
  -- Observational equality is project-wide HoTT terminology.
  someSegment == "OEq" ||
  someSegment == "opp" ||  -- Interval opposite (cubical convention)
  someSegment == "par" ||  -- parallel reduction (project-wide)
  someSegment == "one" ||  -- semiring multiplicative identity
  someSegment == "sym" ||  -- symmetry (math convention)
  someSegment == "beq" ||  -- boolean equality (Lean convention)
  someSegment == "nat" ||  -- natural number (math convention)
  someSegment == "run"     -- apply/execute (common project convention)

/-- Detect whether a name segment violates the project naming
discipline (single/two/three-character identifiers, non-ASCII).
Returns the rendered offending segment, or none if compliant. -/
def offendingNameSegment (renderedSegment : String) : Option String :=
  if renderedSegment.isEmpty then
    some renderedSegment
  else if !renderedSegment.toList.all (fun someChar => someChar.toNat < 128) then
    some renderedSegment
  else if renderedSegment.length < 4 &&
          !isWhitelistedShortIdentifier renderedSegment then
    some renderedSegment
  else
    none

/-- Get the LAST string segment of a name — the actual identifier
that the developer chose, distinct from the namespace path.  CLAUDE.md
naming discipline applies to identifier choice, not to organizational
paths (e.g., the namespace `HoTT.HIT.S1.base` has identifier `base`,
which is too short, but `HIT` and `S1` are organizational folders the
user is allowed to name short for math conventions). -/
def lastStringSegment (someName : Name) : Option String :=
  match someName with
  | .str _ partString => some partString
  | _ => none

/-- A name is naming-discipline-compliant iff its terminal user
segment passes `offendingNameSegment`.  Numeric tail segments are
recursor/hygiene noise; intermediate namespace segments are
organizational choices.  Only the final identifier is policed. -/
def offendingNameSegments (someName : Name) : Array String :=
  match lastStringSegment someName with
  | none => #[]
  | some lastSegment =>
      match offendingNameSegment lastSegment with
      | some bad => #[bad]
      | none => #[]

/-- Names emitted by Lean's elaborator (under-bound match aux, hygiene
suffixes, structure projections) carry segments that look like
discipline violations but are mechanically necessary.  Filter them
before counting violations. -/
def isLeanGeneratedNamingPattern (someName : Name) : Bool :=
  let rendered := someName.toString
  someName.isInternal ||
  rendered.contains '«' ||
  rendered.contains '»' ||
  rendered.endsWith ".rec" ||
  rendered.endsWith ".recOn" ||
  rendered.endsWith ".casesOn" ||
  rendered.endsWith ".below" ||
  rendered.endsWith ".brecOn" ||
  rendered.endsWith ".binductionOn" ||
  rendered.endsWith ".ndrec" ||
  rendered.endsWith ".sizeOf" ||
  rendered.endsWith ".inj" ||
  rendered.endsWith ".injEq" ||
  rendered.endsWith ".eq_def" ||
  rendered.endsWith ".sizeOf_spec" ||
  rendered.endsWith ".repr" ||
  rendered.endsWith ".instRepr" ||
  rendered.endsWith ".go" ||
  rendered.endsWith ".eq" ||
  rendered.contains '.' &&
    (rendered.endsWith ".mk" || rendered.endsWith ".match")

/-- Build-failing naming gate.  Walks every user-defined declaration
under a namespace and reports identifiers that violate the project
naming discipline.  Reports ALL violations in one error. -/
elab "#assert_namespace_naming " namespaceSyntax:ident : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let mut violations : Array (Name × Array String) := #[]
  let mut auditedCount : Nat := 0
  for (declName, declInfo) in environment.constants.toList do
    if Name.isWithinNamespace namespaceName declName &&
        !isGeneratedOrToolingName declName &&
        !isLeanGeneratedNamingPattern declName &&
        isNamespaceAuditTarget declInfo then
      auditedCount := auditedCount + 1
      let badSegments := offendingNameSegments declName
      if !badSegments.isEmpty then
        violations := violations.push (declName, badSegments)
  if violations.isEmpty then
    logInfo m!"naming discipline ok: {namespaceName} ({auditedCount} declarations)"
  else
    let perDeclLines := violations.toList.map fun (declName, segments) =>
      let segmentsRendered := String.intercalate ", " segments.toList
      s!"  - {declName}: bad segments [{segmentsRendered}]"
    let header :=
      s!"naming discipline FAILED for {namespaceName}: " ++
      s!"{violations.size} of {auditedCount} decls violate naming"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Hypothesis-as-postulate detector

CLAUDE.md "Forbidden reasoning patterns" bans theorems that take an
unprovable principle as a hypothesis (e.g.,
`theorem foo (univ : Univalence) : ...`).  Such theorems vacuously
"ship" their conclusion conditional on an input that cannot be
constructed at the kernel layer.

This gate flags any theorem whose declared signature mentions one of
the load-bearing zero-axiom HoTT theorems as a hypothesis type.  The
named theorems are themselves provable in lean-fx-2; using them as
hypotheses is suspicious because either the caller can already
discharge them or the dependency should be documented explicitly. -/

/-- Names whose use as a HYPOTHESIS in a theorem signature is
suspicious.  These are all themselves provable in the kernel; taking
them as a hypothesis duplicates an already-discharged fact. -/
def bannedHypothesisType (someName : Name) : Bool :=
  someName == `LeanFX2.Univalence ||
  someName == `LeanFX2.UnivalenceHet ||
  someName == `LeanFX2.funext ||
  someName == `LeanFX2.FunextHet

/-- Walk a theorem's declared type and check whether any
`bannedHypothesisType` constant appears.  Conservative: any use, not
just hypothesis position, is flagged.  In practice these names appear
only as full hypothesis types in suspect signatures. -/
def detectsPostulateHypothesis
    (environment : Environment) (someName : Name) (someInfo : ConstantInfo) :
    Option Name :=
  let _ := environment
  let _ := someName
  let typeReferences :=
    someInfo.type.foldConsts NameSet.empty (fun referencedName references =>
      references.insert referencedName)
  typeReferences.toList.find? bannedHypothesisType

/-- Build-failing gate: no theorem signature in the namespace may
mention a banned hypothesis type. -/
elab "#assert_no_postulate_hypothesis " namespaceSyntax:ident : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array (Name × Name) := #[]
  for targetName in targetNames do
    match environment.find? targetName with
    | none => continue
    | some constantInfo =>
        match detectsPostulateHypothesis environment targetName constantInfo with
        | some banned => violations := violations.push (targetName, banned)
        | none => pure ()
  if violations.isEmpty then
    logInfo m!"hypothesis-as-postulate audit ok: {namespaceName} ({targetNames.size} declarations)"
  else
    let perDeclLines := violations.toList.map fun (declName, bannedName) =>
      s!"  - {declName}: takes {bannedName} as hypothesis (already provable, banned)"
    let header :=
      s!"hypothesis-as-postulate audit FAILED for {namespaceName}: " ++
      s!"{violations.size} of {targetNames.size} decls violate discipline"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Per-namespace decl-count snapshot

Track decl count by sub-namespace.  Useful for catching coverage
regressions: if a future change removes 100 decls from `LeanFX2.Term`,
the snapshot makes that visible.  Strictly informational. -/

/-- Build a list of (sub-namespace, decl-count) pairs at depth 2 below
`LeanFX2.*`.  E.g., counts decls under `LeanFX2.Term`, `LeanFX2.Conv`,
... separately. -/
def computeSubNamespaceCounts (environment : Environment) : Array (Name × Nat) :=
  let pairs := environment.constants.toList.foldl
    (init := (#[] : Array (Name × Nat)))
    (fun acc (declName, declInfo) =>
      if Name.isWithinNamespace `LeanFX2 declName &&
          !isGeneratedOrToolingName declName &&
          isNamespaceAuditTarget declInfo then
        let parts := declName.componentsRev.reverse
        match parts with
        | _ :: secondLevel :: _ =>
            let subNamespace := `LeanFX2 ++ Name.mkSimple secondLevel.toString
            -- Increment count for subNamespace
            let existingIndex := acc.findIdx? (fun (storedName, _) => storedName == subNamespace)
            match existingIndex with
            | some idx =>
                acc.modify idx (fun (storedName, count) => (storedName, count + 1))
            | none => acc.push (subNamespace, 1)
        | _ => acc
      else acc)
  pairs

/-- Print the decl-count snapshot for `LeanFX2.*` sub-namespaces. -/
elab "#audit_subnamespace_counts" : command => do
  let environment ← getEnv
  let pairs := computeSubNamespaceCounts environment
  let totalCount := pairs.foldl (fun running (_, count) => running + count) 0
  let perLine := pairs.toList.map fun (subNamespace, count) =>
    s!"    {subNamespace}: {count}"
  let header :=
    "──────────── SUB-NAMESPACE DECL COUNTS ────────────"
  let footer :=
    "─────────────────────────────────────────────────────"
  let totalLine := s!"  Total LeanFX2 decls: {totalCount}"
  logInfo
    (String.intercalate "\n"
      ([header, totalLine, "  Per-namespace:"] ++ perLine ++ [footer]))

end LeanFX2.Tools
