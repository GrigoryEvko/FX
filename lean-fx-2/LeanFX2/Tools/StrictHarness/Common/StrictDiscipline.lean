import LeanFX2.Tools.StrictHarness.Common.AuditCounts

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

end LeanFX2.Tools
