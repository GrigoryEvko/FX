import LeanFX2.Tools.StrictHarness.Common.AuditCounts

namespace LeanFX2.Tools

open Lean Elab Command

/-- The pre-FX1 Lean-kernel scaffold namespace.  It remains buildable and
audited, but it is not the planned trusted Lean-in-FX path. -/
def isLegacyLeanKernelScaffoldModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.Lean.Kernel).isPrefixOf moduleName

/-- Rich-to-FX1 bridge modules translate expressive LeanFX2 fragments into the
FX1 checker/metatheory cone.  They are production-bearing bridge code, but not
part of rich production and not part of the FX1 root itself. -/
def isFX1BridgeModuleName (moduleName : Name) : Bool :=
  (`LeanFX2.FX1Bridge).isPrefixOf moduleName

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
    !isFX1BridgeModuleName moduleName &&
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
    moduleName == `LeanFX2.FX1Bridge ||
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
    (directImportRecord.sourceModuleName == `LeanFX2.FX1Bridge &&
      (`LeanFX2.FX1Bridge).isPrefixOf directImportRecord.importedModuleName) ||
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

end LeanFX2.Tools
