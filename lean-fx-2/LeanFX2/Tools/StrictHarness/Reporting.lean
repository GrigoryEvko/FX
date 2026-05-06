import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census
import LeanFX2.Tools.StrictHarness.DeclShape
import LeanFX2.Tools.StrictHarness.AxiomAdjacent
import LeanFX2.Tools.StrictHarness.TrustEscape
import LeanFX2.Tools.StrictHarness.MetaLevel

namespace LeanFX2.Tools

open Lean Elab Command

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

/-! ## Headline refl-fragment detector

This detector tracks the specific anti-pattern where a headline principle name
(`Univalence`, `funext`, and heterogeneous variants) is backed by one of the
manufactured raw-alignment reduction rules.  Current debt is budgeted so the
build stays green, but new headline refl-fragment claims cannot accumulate
silently.
-/

/-- Names of manufactured Step rules used to turn canonical/raw-aligned
witnesses into headline HoTT principles. -/
def isManufacturedWitnessStepRule (dependencyName : Name) : Bool :=
  dependencyName == `LeanFX2.Step.eqType ||
    dependencyName == `LeanFX2.Step.eqArrow ||
    dependencyName == `LeanFX2.Step.eqTypeHet ||
    dependencyName == `LeanFX2.Step.eqArrowHet ||
    dependencyName == `LeanFX2.Step.par.eqType ||
    dependencyName == `LeanFX2.Step.par.eqArrow ||
    dependencyName == `LeanFX2.Step.par.eqTypeHet ||
    dependencyName == `LeanFX2.Step.par.eqArrowHet

/-- Headline theorem names that must not pretend a manufactured/rfl-fragment
rule is the full mathematical principle without being counted by the harness. -/
def isHeadlinePrincipleClaimName (declarationName : Name) : Bool :=
  let lastSegment := Name.lastSegmentString declarationName
  lastSegment == "Univalence" ||
    lastSegment == "UnivalenceHet" ||
    lastSegment == "funext" ||
    lastSegment == "FunextHet"

/-- Manufactured Step dependencies in one declaration's transitive closure. -/
def collectManufacturedWitnessStepDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames := collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun manufacturedDependencies dependencyName =>
      if isManufacturedWitnessStepRule dependencyName then
        manufacturedDependencies.push dependencyName
      else
        manufacturedDependencies)

/-- Build-failing budget gate for headline principles backed by manufactured
Step rules.  The budget counts declarations, not individual dependencies. -/
elab "#assert_headline_refl_fragment_budget " namespaceSyntax:ident
    claimBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let claimBudget := claimBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array (Name × Array Name) := #[]
  for targetName in targetNames do
    if isHeadlinePrincipleClaimName targetName then
      let manufacturedDependencies :=
        collectManufacturedWitnessStepDependencies environment targetName
      if !manufacturedDependencies.isEmpty then
        violations := violations.push (targetName, manufacturedDependencies)
  recordAuditCount `headline_refl_fragment violations.size
  if violations.size <= claimBudget then
    let successMessage :=
      s!"headline refl-fragment budget ok: {namespaceName} " ++
      s!"({violations.size}/{claimBudget} headline claims depend on " ++
      "manufactured Step rules)"
    logInfo successMessage
  else
    let perDeclLines := violations.toList.map fun (declName, dependencies) =>
      let renderedDependencies :=
        String.intercalate ", " (dependencies.toList.map toString)
      s!"  - {declName}: manufactured Step dependencies [{renderedDependencies}]"
    let header :=
      s!"headline refl-fragment budget FAILED for {namespaceName}: " ++
      s!"{violations.size} claims exceed budget {claimBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Broad manufactured-Step dependent count

The existing `#assert_headline_refl_fragment_budget` filters by name —
it only counts decls whose final name segment is `Univalence`,
`UnivalenceHet`, `funext`, or `FunextHet`.  A wrapper named
`MyTheorem := Univalence` slips through that gate cleanly because its
name segment is `MyTheorem`, not `Univalence`.

This gate widens the lens to ALL decls in the namespace.  It counts
every declaration whose transitive dependency closure mentions a
manufactured Step rule, except for an allowlist of decls that are
expected to thread those rules structurally:

* The manufactured Step rules themselves (`Step.eqType`, etc.).
* Their `Step.par.*` mirrors.
* The headline-named claims already counted by the headline gate.
* Confluence / Cd / CdLemma / Diamond / ChurchRosser internal
  scaffolding (each has one match arm per Step rule).
* Bridge raw-projection scaffolding under `Reduction.RawPar*` /
  `RawCd*`.

Anything else that mentions a manufactured rule transitively is a
wrapper — a renamed restatement of a refl-fragment claim.  Pinning
the count makes wrapper accumulation visible.
-/

/-- Whether a declaration is in the documented allowlist of decls
expected to thread manufactured Step rules structurally.  Membership
prefixes are by full prefix-of name. -/
def isManufacturedStepStructuralDependent (declName : Name) : Bool :=
  -- The manufactured rules themselves and their parallel mirrors.
  declName == `LeanFX2.Step.eqType ||
    declName == `LeanFX2.Step.eqArrow ||
    declName == `LeanFX2.Step.eqTypeHet ||
    declName == `LeanFX2.Step.eqArrowHet ||
    declName == `LeanFX2.Step.par.eqType ||
    declName == `LeanFX2.Step.par.eqArrow ||
    declName == `LeanFX2.Step.par.eqTypeHet ||
    declName == `LeanFX2.Step.par.eqArrowHet ||
    -- Headline claims already counted by the headline gate (do not
    -- double-count them in this broader census).
    isHeadlinePrincipleClaimName declName ||
    -- Confluence / reduction scaffolding that pattern-matches one
    -- arm per Step rule.
    (`LeanFX2.Confluence).isPrefixOf declName ||
    (`LeanFX2.Reduction.Cd).isPrefixOf declName ||
    (`LeanFX2.Reduction.CdLemma).isPrefixOf declName ||
    (`LeanFX2.Reduction.Diamond).isPrefixOf declName ||
    (`LeanFX2.Reduction.ChurchRosser).isPrefixOf declName ||
    -- Raw-bridge scaffolding mirroring typed Step.par into RawStep.par.
    (`LeanFX2.Reduction.RawPar).isPrefixOf declName ||
    (`LeanFX2.Reduction.RawCd).isPrefixOf declName ||
    (`LeanFX2.Reduction.Compat).isPrefixOf declName ||
    (`LeanFX2.Reduction.ParStar).isPrefixOf declName ||
    -- HoTT and Cubical headline-adjacent files where the manufactured
    -- rules are the explicit subject (Conv.fromStep applications).
    (`LeanFX2.HoTT.Univalence).isPrefixOf declName ||
    (`LeanFX2.HoTT.UnivalenceHet).isPrefixOf declName ||
    (`LeanFX2.Cubical.PathLemmas).isPrefixOf declName ||
    (`LeanFX2.Cubical.FunextHet).isPrefixOf declName

/-- Build-failing budget gate for the broad manufactured-Step dependent
count.  Pins current count; future wrapper decls that depend on a
manufactured rule outside the allowlist push the count above the
ceiling and fail the build. -/
elab "#assert_broad_manufactured_step_dependent_budget "
    namespaceSyntax:ident dependentBudgetSyntax:num : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let dependentBudget := dependentBudgetSyntax.getNat
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut violations : Array (Name × Array Name) := #[]
  for targetName in targetNames do
    if isManufacturedStepStructuralDependent targetName then
      continue
    else
      let manufacturedDependencies :=
        collectManufacturedWitnessStepDependencies environment targetName
      if !manufacturedDependencies.isEmpty then
        violations := violations.push (targetName, manufacturedDependencies)
  recordAuditCount `broad_manufactured_step_dependent violations.size
  if violations.size <= dependentBudget then
    logInfo
      (s!"broad manufactured-Step dependent budget ok: {namespaceName} " ++
      s!"({violations.size}/{dependentBudget} non-allowlisted decls " ++
      "depend on manufactured Step rules)")
  else
    let perDeclLines := violations.toList.map fun (declName, dependencies) =>
      let renderedDependencies :=
        String.intercalate ", " (dependencies.toList.map toString)
      s!"  - {declName}: manufactured Step deps [{renderedDependencies}]"
    let header :=
      s!"broad manufactured-Step dependent budget FAILED for " ++
      s!"{namespaceName}: {violations.size} non-allowlisted dependents " ++
      s!"exceed budget {dependentBudget}"
    throwError (header ++ "\n" ++ String.intercalate "\n" perDeclLines)

/-! ## Staged FX1 axiom leak detector

FX1Bridge modules may use object-level `Declaration.axiomDecl` entries while a
rich feature is still only staged as a Bridge fragment.  Regular rich/root
production declarations must not depend on those staged placeholders: doing so
would silently promote Bridge-only evidence into rich production.
-/

/-- Whether a dependency is one of the FX1 declaration constructors that admits
object-level staged axioms. -/
def isStagedFX1AxiomDeclarationDependency (dependencyName : Name) : Bool :=
  dependencyName == `LeanFX2.FX1.Declaration.axiomDecl ||
    dependencyName == `LeanFX2.FX1.Declaration.WellTyped.axiomDecl

/-- Declarations allowed to mention staged FX1 axiom placeholders directly.

FX1 itself defines the declaration language and release well-formedness rules.
FX1Bridge is the explicit staging boundary.  Everything else must stay clear of
these constructors until it has a real root certificate. -/
def mayUseStagedFX1AxiomDeclarations (declarationName : Name) : Bool :=
  (`LeanFX2.FX1).isPrefixOf declarationName ||
    (`LeanFX2.FX1Bridge).isPrefixOf declarationName

/-- Collect staged FX1 axiom dependencies from one declaration's transitive
dependency closure. -/
def collectStagedFX1AxiomDependencies
    (environment : Environment) (targetName : Name) :
    Array Name :=
  let dependencyNames := collectDependencies environment targetName (includeStdlib := true)
  dependencyNames.toList.foldl
    (init := (#[] : Array Name))
    (fun stagedDependencies dependencyName =>
      if isStagedFX1AxiomDeclarationDependency dependencyName then
        stagedDependencies.push dependencyName
      else
        stagedDependencies)

/-- Build-failing gate: staged FX1 object-level axioms may not leak out of
FX1/FX1Bridge into rich or root production declarations. -/
elab "#assert_no_root_staged_axiom_leak " namespaceSyntax:ident : command => do
  let environment ← getEnv
  let namespaceName := namespaceSyntax.getId
  let targetNames := namespaceAuditTargets environment namespaceName
  let mut scannedDeclarationCount : Nat := 0
  let mut violations : Array (Name × Array Name) := #[]
  for targetName in targetNames do
    if mayUseStagedFX1AxiomDeclarations targetName then
      continue
    else
      scannedDeclarationCount := scannedDeclarationCount + 1
      let stagedDependencies :=
        collectStagedFX1AxiomDependencies environment targetName
      if !stagedDependencies.isEmpty then
        violations := violations.push (targetName, stagedDependencies)
  if violations.isEmpty then
    let skippedDeclarationCount := targetNames.size - scannedDeclarationCount
    let successMessage :=
      s!"root staged-axiom leak audit ok: {namespaceName} " ++
      s!"({scannedDeclarationCount} declarations scanned, " ++
      s!"{skippedDeclarationCount} FX1/bridge declarations skipped)"
    logInfo successMessage
  else
    let perDeclLines := violations.toList.map fun (declName, dependencies) =>
      let renderedDependencies :=
        String.intercalate ", " (dependencies.toList.map toString)
      s!"  - {declName}: staged FX1 axiom dependencies [{renderedDependencies}]"
    let header :=
      s!"root staged-axiom leak audit FAILED for {namespaceName}: " ++
      s!"{violations.size} of {scannedDeclarationCount} scanned decls " ++
      "depend on Bridge-only FX1 axiom staging"
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
