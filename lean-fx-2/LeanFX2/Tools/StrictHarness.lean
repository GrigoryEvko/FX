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
counterpart in the current snapshot.  Each entry corresponds to a
RawStep.par cong/β rule whose typed Step.par mirror has not been
shipped yet (the raw cubical/HoTT/refine/record/codata/session/effect/
type-code layers landed before the corresponding typed layer was wired
up).  Tracking these as documented exceptions means the parity gate
still catches NEW raw-only ctors going forward, while the 41 existing
gaps are recorded explicitly rather than being silently allowed.

Discipline for moving an entry OUT of this list: add the matching
`Step.par.X` constructor in `Reduction/ParRed.lean`, mirror the
`Confluence/RawCd.lean` and `Confluence/RawCdLemma.lean` entries to
`Confluence/Cd.lean` and `Confluence/CdLemma.lean`, then delete the
entry below. -/
def isDocumentedRawOnlyParity (rawCtorName : Name) : Bool :=
  let suffix := Name.lastSegmentString rawCtorName
  -- Section A: cubical / interval cong rules (typed mirrors pending D2.5
  -- typed cascade — currently only path-app and Glue-elim β have typed
  -- mirrors; cong rules and other primitives ship raw-only).
  suffix == "intervalOppCong" ||
  suffix == "intervalMeetCong" ||
  suffix == "intervalJoinCong" ||
  suffix == "pathLamCong" ||
  suffix == "pathAppCong" ||
  suffix == "glueIntroCong" ||
  suffix == "glueElimCong" ||
  suffix == "transpCong" ||
  suffix == "hcompCong" ||
  -- Section B: HoTT observational-equality cong rules (typed mirrors
  -- pending D2.6 cascade — eqType and eqArrow already have typed Step
  -- counterparts; remaining oeq cong/funext rules ship raw-only).
  suffix == "oeqReflCong" ||
  suffix == "oeqJCong" ||
  suffix == "oeqFunextCong" ||
  -- Section C: strict identity cong rules (typed mirrors pending; the
  -- strict-identity layer is currently raw-only scaffolding).
  suffix == "idStrictReflCong" ||
  suffix == "idStrictRecCong" ||
  -- Section D: equivalence cong rules (typed equivalence types not yet
  -- introduced as Term ctors; equiv lives in raw form only).
  suffix == "equivIntroCong" ||
  suffix == "equivAppCong" ||
  -- Section E: refinement type cong + β rules (typed Term has no refine
  -- ctor yet; D5.6 refinement types pending).
  suffix == "refineIntroCong" ||
  suffix == "betaRefineElimIntro" ||
  suffix == "betaRefineElimIntroDeep" ||
  suffix == "refineElimCong" ||
  -- Section F: record cong + β rules (typed records pending).
  suffix == "recordIntroCong" ||
  suffix == "betaRecordProjIntro" ||
  suffix == "betaRecordProjIntroDeep" ||
  suffix == "recordProjCong" ||
  -- Section G: codata cong rules (typed codata pending D5.13).
  suffix == "codataUnfoldCong" ||
  suffix == "codataDestCong" ||
  -- Section H: session protocol cong rules (typed sessions pending D5.11).
  suffix == "sessionSendCong" ||
  suffix == "sessionRecvCong" ||
  -- Section I: effect-perform cong rule (typed effect handlers pending
  -- D5.10).
  suffix == "effectPerformCong" ||
  -- Section J: parametric type-code cong rules (CUMUL-2 cumulativity
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
  -- Section K: refl cong rule (typed Term.refl uses different reduction
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

end LeanFX2.Tools
