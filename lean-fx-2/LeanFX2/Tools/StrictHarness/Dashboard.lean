import LeanFX2.Tools.StrictHarness.Common
import LeanFX2.Tools.StrictHarness.Census
import LeanFX2.Tools.StrictHarness.DeclShape
import LeanFX2.Tools.StrictHarness.AxiomAdjacent
import LeanFX2.Tools.StrictHarness.TrustEscape
import LeanFX2.Tools.StrictHarness.MetaLevel
import LeanFX2.Tools.StrictHarness.Reporting

namespace LeanFX2.Tools

open Lean Elab Command

/-! ## Aggregate semantic-debt dashboard

End-of-build banner aggregating EVERY signature-debt budget into one
prominent multi-line report.  Strictly informational; the actual
build-failing happens via the per-budget `#assert_*_budget` gates above.
This is the visibility layer that surfaces today's debt counts amid
build noise so a reader skimming the build log can see at a glance:

* total declarations audited / clean / failed
* schematic payload census across `Ty` and `Term`
* every semantic-signature debt class with current count
* bridge coverage ratio (rich Term ctor → FX1 encoding)
* headline refl-fragment claims still depending on manufactured Step rules

Wiring: invoked as the final command in `Tools/AuditAll.lean` so the
dashboard renders LAST in the build log, after every gate has already
fired.  When a budget rises beyond its ceiling, the corresponding gate
errors out before the dashboard is rendered, so a passing build that
shows the dashboard is one in which all ratchets held.
-/

/-- Format one debt row with right-justified count.  Keeps the dashboard
columns aligned without a manual spacing table. -/
def formatDebtRow (label : String) (count : Nat) : String :=
  let countText := toString count
  let labelWidth : Nat := 50
  let labelPaddingNeeded :=
    if label.length < labelWidth then labelWidth - label.length else 1
  let labelPadding := String.ofList (List.replicate labelPaddingNeeded ' ')
  s!"    {label}{labelPadding}{countText}"

/-- Aggregate semantic-debt dashboard over a Term inductive, a Ty
inductive, and a top-level namespace.  All counts are read live from the
environment via the existing per-gate record collectors; no separate
state is maintained.  The dashboard does not throw — it logs at info
level so the build keeps going regardless of debt levels.

Layout: one prominent banner with five sections.

* Audited declarations: total / clean / failed across the namespace.
* Schematic payload census: explicit `RawTerm` and `Nat` payloads in
  Ty and Term constructors.
* Semantic signature debt: thirteen rows, one per known fake-typing
  class (mode discipline, dependent eliminator motive, unit-typed
  proof placeholder, modal no-op, session no-advance, equiv coherence,
  Ty raw endpoint, Ty unstructured schema, transport linkage, glue
  schema, effect schema, session schema, hcomp Kan).
* Bridge coverage: encoded ctor count over total ctor count, plus
  unbridged ctor count.
* Headline refl-fragment claims: count of declarations in the
  namespace whose transitive closure depends on a manufactured
  Univalence / funext Step rule.

When all numbers are at their current pinned budgets the dashboard
shows the project's debt floor in one place; when work reduces a
budget, the corresponding row drops without manual edits. -/
elab "#audit_debt_dashboard " termInductiveSyntax:ident
    tyInductiveSyntax:ident namespaceSyntax:ident : command => do
  let environment ← getEnv
  let termInductiveName := termInductiveSyntax.getId
  let tyInductiveName := tyInductiveSyntax.getId
  let namespaceName := namespaceSyntax.getId
  -- Schematic payload census across Ty and Term constructors.
  let tyPayloadRecords :=
    schematicPayloadRecordsForInductive environment tyInductiveName
  let tyPayloadTotals := totalSchematicPayloadCounts tyPayloadRecords
  let termPayloadRecords :=
    schematicPayloadRecordsForInductive environment termInductiveName
  let termPayloadTotals := totalSchematicPayloadCounts termPayloadRecords
  -- Per-debt-class counts.
  let modeDebtCount :=
    (modeDisciplineDebtRecordsForInductive environment termInductiveName).size
  let motiveDebtCount :=
    (dependentEliminatorDebtRecordsForInductive
      environment termInductiveName).size
  let unitPlaceholderDebtCount :=
    (unitPlaceholderDebtRecordsForInductive
      environment termInductiveName).size
  let modalNoopDebtCount :=
    (modalNoopDebtRecordsForInductive environment termInductiveName).size
  let sessionNoAdvanceDebtCount :=
    (sessionNoAdvanceDebtRecordsForInductive
      environment termInductiveName).size
  let equivCoherenceDebtCount :=
    (equivCoherenceDebtRecordsForInductive
      environment termInductiveName).size
  let tyRawEndpointDebtCount :=
    (tyRawEndpointDebtRecordsForInductive
      environment tyInductiveName).size
  let tyUnstructuredSchemaDebtCount :=
    (tyUnstructuredSchemaDebtRecordsForInductive
      environment tyInductiveName).size
  let transportLinkageDebtCount :=
    (transportLinkageDebtRecordsForInductive
      environment termInductiveName).size
  let glueSchemaDebtCount :=
    (glueSchemaDebtRecordsForInductive environment termInductiveName).size
  let effectSchemaDebtCount :=
    (effectSchemaDebtRecordsForInductive
      environment termInductiveName).size
  let sessionSchemaDebtCount :=
    (sessionSchemaDebtRecordsForInductive
      environment termInductiveName).size
  let hcompKanDebtCount :=
    (hcompKanDebtRecordsForInductive environment termInductiveName).size
  -- Bridge coverage.
  let totalCtorCount :=
    (getInductiveConstructorNames environment termInductiveName).size
  let bridgeUncoveredCount :=
    (bridgeCoverageDebtRecordsForInductive
      environment termInductiveName).size
  let bridgeCoveredCount :=
    if totalCtorCount >= bridgeUncoveredCount then
      totalCtorCount - bridgeUncoveredCount
    else 0
  -- Step.par cong-rule coverage matrix.
  let stepParCongUncoveredCount :=
    (stepParCongCoverageDebtRecordsForInductive
      environment termInductiveName).size
  let stepParCongCoveredCount :=
    if totalCtorCount >= stepParCongUncoveredCount then
      totalCtorCount - stepParCongUncoveredCount
    else 0
  -- Conv cong-rule coverage matrix.
  let convCongUncoveredCount :=
    (convCongCoverageDebtRecordsForInductive
      environment termInductiveName).size
  let convCongCoveredCount :=
    if totalCtorCount >= convCongUncoveredCount then
      totalCtorCount - convCongUncoveredCount
    else 0
  -- Headline refl-fragment claims.
  let mut headlineReflFragmentCount : Nat := 0
  let mut broadManufacturedDependentCount : Nat := 0
  let mut castOperatorDependentCount : Nat := 0
  let mut forbiddenShapeCount : Nat := 0
  let mut singleStepConvClaimCount : Nat := 0
  let targetNames := namespaceAuditTargets environment namespaceName
  for targetName in targetNames do
    if isHeadlinePrincipleClaimName targetName then
      let manufacturedDependencies :=
        collectManufacturedWitnessStepDependencies environment targetName
      if !manufacturedDependencies.isEmpty then
        headlineReflFragmentCount := headlineReflFragmentCount + 1
    else if !isManufacturedStepStructuralDependent targetName then
      let manufacturedDependencies :=
        collectManufacturedWitnessStepDependencies environment targetName
      if !manufacturedDependencies.isEmpty then
        broadManufacturedDependentCount := broadManufacturedDependentCount + 1
    if isKernelTierProductionDecl targetName then
      let castDependencies :=
        collectCastOperatorDependencies environment targetName
      if !castDependencies.isEmpty then
        castOperatorDependentCount := castOperatorDependentCount + 1
      match forbiddenDeclShape? environment targetName with
      | some _ => forbiddenShapeCount := forbiddenShapeCount + 1
      | none => pure ()
    match environment.find? targetName with
    | some constantInfo =>
        if claimsConvType constantInfo then
          match constantInfo.value? with
          | some bodyExpr =>
              if isSingleStepConvBody bodyExpr then
                singleStepConvClaimCount := singleStepConvClaimCount + 1
          | none => pure ()
    | none => pure ()
  -- All-raw-payload Term ctor count.
  let allRawPayloadCount :=
    (allRawPayloadDebtRecordsForInductive
      environment termInductiveName).size
  -- Reduction.Compat coverage debt for Step.par cong rules.
  let reductionCompatUncoveredCount :=
    (reductionCompatCoverageDebtRecordsForInductive
      environment `LeanFX2.Step.par).size
  -- toRaw projection coverage.
  let toRawUncoveredCount :=
    (toRawCoverageDebtRecordsForInductive
      environment termInductiveName).size
  let toRawCoveredCount :=
    if totalCtorCount >= toRawUncoveredCount then
      totalCtorCount - toRawUncoveredCount
    else 0
  -- IsClosedTy parity for scope-independent Ty ctors.
  let isClosedTyParityUncoveredCount :=
    (isClosedTyParityDebtRecordsForInductive
      environment tyInductiveName).size
  -- Inductive ctor count snapshots.
  let termCtorCount :=
    (getInductiveConstructorNames environment termInductiveName).size
  let tyCtorCount :=
    (getInductiveConstructorNames environment tyInductiveName).size
  let stepCtorCount :=
    (getInductiveConstructorNames environment `LeanFX2.Step).size
  let stepParCtorCount :=
    (getInductiveConstructorNames environment `LeanFX2.Step.par).size
  let rawTermCtorCount :=
    (getInductiveConstructorNames environment `LeanFX2.RawTerm).size
  -- Axiom-adjacent dependency censuses.
  let mut inhabitedDependentCount : Nat := 0
  let mut heqResultTypeCount : Nat := 0
  let mut decideDependentCount : Nat := 0
  let mut subsingletonDependentCount : Nat := 0
  let mut matchCompilerEquationCount : Nat := 0
  let mut rflOnNonTrivialNameCount : Nat := 0
  let mut universePolymorphicCount : Nat := 0
  let mut quotDependentCount : Nat := 0
  let mut accDependentCount : Nat := 0
  let mut leanMetaDependentCount : Nat := 0
  -- Lean-trust-escape and shape detectors (this batch).
  let mut coeDependentCount : Nat := 0
  let mut ofNatDependentCount : Nat := 0
  let mut subtypeDependentCount : Nat := 0
  let mut functionPropertyDependentCount : Nat := 0
  let mut eqRewritingDependentCount : Nat := 0
  let mut reducibleDeclCount : Nat := 0
  let mut falseResultTypeCount : Nat := 0
  let mut dependentPairDependentCount : Nat := 0
  let mut classicalReasoningDependentCount : Nat := 0
  let mut apiTypeclassDependentCount : Nat := 0
  let mut ioEffectDependentCount : Nat := 0
  let mut anonymousProjectionDependentCount : Nat := 0
  for targetName in targetNames do
    if !isKernelTierProductionDecl targetName then
      continue
    if !(collectInhabitedDependencies environment targetName).isEmpty then
      inhabitedDependentCount := inhabitedDependentCount + 1
    match environment.find? targetName with
    | some constantInfo =>
        if claimsHEqInResultType constantInfo then
          heqResultTypeCount := heqResultTypeCount + 1
        if hasNonTrivialNameSuffix targetName then
          match constantInfo.value? with
          | some bodyExpr =>
              if isRflOnlyBody bodyExpr then
                rflOnNonTrivialNameCount := rflOnNonTrivialNameCount + 1
          | none => pure ()
    | none => pure ()
    if !(collectDecideDependencies environment targetName).isEmpty then
      decideDependentCount := decideDependentCount + 1
    if !(collectSubsingletonDependencies environment targetName).isEmpty then
      subsingletonDependentCount := subsingletonDependentCount + 1
    if isMatchCompilerEquationName targetName then
      matchCompilerEquationCount := matchCompilerEquationCount + 1
    if !(collectQuotDependencies environment targetName).isEmpty then
      quotDependentCount := quotDependentCount + 1
    if !(collectAccDependencies environment targetName).isEmpty then
      accDependentCount := accDependentCount + 1
    if !(collectLeanMetaDependencies environment targetName).isEmpty then
      leanMetaDependentCount := leanMetaDependentCount + 1
    if !(collectCoeDependencies environment targetName).isEmpty then
      coeDependentCount := coeDependentCount + 1
    if !(collectOfNatDependencies environment targetName).isEmpty then
      ofNatDependentCount := ofNatDependentCount + 1
    if !(collectSubtypeDependencies environment targetName).isEmpty then
      subtypeDependentCount := subtypeDependentCount + 1
    if !(collectFunctionPropertyDependencies environment targetName).isEmpty then
      functionPropertyDependentCount := functionPropertyDependentCount + 1
    if !(collectEqRewritingDependencies environment targetName).isEmpty then
      eqRewritingDependentCount := eqRewritingDependentCount + 1
    if hasAbbrevReducibilityHint environment targetName then
      reducibleDeclCount := reducibleDeclCount + 1
    if !(collectDependentPairDependencies environment targetName).isEmpty then
      dependentPairDependentCount := dependentPairDependentCount + 1
    if !(collectClassicalReasoningDependencies environment targetName).isEmpty then
      classicalReasoningDependentCount := classicalReasoningDependentCount + 1
    if !(collectApiTypeclassDependencies environment targetName).isEmpty then
      apiTypeclassDependentCount := apiTypeclassDependentCount + 1
    if !(collectIOEffectDependencies environment targetName).isEmpty then
      ioEffectDependentCount := ioEffectDependentCount + 1
    if !(collectAnonymousProjectionDependencies environment targetName).isEmpty then
      anonymousProjectionDependentCount := anonymousProjectionDependentCount + 1
    match environment.find? targetName with
    | some constantInfo =>
        if hasUniversePolymorphicSort constantInfo.type then
          universePolymorphicCount := universePolymorphicCount + 1
        if claimsFalseResultType constantInfo then
          falseResultTypeCount := falseResultTypeCount + 1
    | none => pure ()
  -- Strict-audit totals across the namespace.
  let mut auditTotalCount : Nat := 0
  let mut auditCleanCount : Nat := 0
  for targetName in targetNames do
    auditTotalCount := auditTotalCount + 1
    match environment.find? targetName with
    | none => continue
    | some constantInfo =>
        let violations :=
          classifyStrictViolations environment targetName constantInfo
        if violations.isEmpty then
          auditCleanCount := auditCleanCount + 1
  let auditFailedCount :=
    if auditTotalCount >= auditCleanCount then
      auditTotalCount - auditCleanCount
    else 0
  -- Total semantic-signature debt across all classes.
  let totalSignatureDebt :=
    modeDebtCount + motiveDebtCount + unitPlaceholderDebtCount +
      modalNoopDebtCount + sessionNoAdvanceDebtCount +
      equivCoherenceDebtCount + tyRawEndpointDebtCount +
      tyUnstructuredSchemaDebtCount + transportLinkageDebtCount +
      glueSchemaDebtCount + effectSchemaDebtCount +
      sessionSchemaDebtCount + hcompKanDebtCount
  -- Compose banner lines.
  let bannerEdge :=
    "════════════════════════════════════════════════════════════"
  let dashHeader :=
    "             lean-fx-2 SEMANTIC DEBT DASHBOARD              "
  let dashLines : List String := [
    bannerEdge,
    dashHeader,
    bannerEdge,
    "  AUDITED DECLARATIONS",
    s!"    Namespace:  {namespaceName}",
    s!"    Total:      {auditTotalCount}",
    s!"    Clean:      {auditCleanCount}",
    s!"    Failed:     {auditFailedCount}",
    "  ──────────────────────────────────────────────────────────",
    "  SCHEMATIC PAYLOAD CENSUS  (raw data laundered into typed)",
    s!"    Ty   ctors: RawTerm={tyPayloadTotals.rawTermPayloadCount}  " ++
      s!"Nat={tyPayloadTotals.natPayloadCount}  " ++
      s!"(payload-bearing ctors: {tyPayloadRecords.size})",
    s!"    Term ctors: RawTerm={termPayloadTotals.rawTermPayloadCount}  " ++
      s!"Nat={termPayloadTotals.natPayloadCount}  " ++
      s!"(payload-bearing ctors: {termPayloadRecords.size})",
    "  ──────────────────────────────────────────────────────────",
    s!"  SEMANTIC SIGNATURE DEBT  (typing-but-not-really-typing): " ++
      s!"{totalSignatureDebt}",
    formatDebtRow
      "Mode discipline (cubical/strict w/o mode premise)"
      modeDebtCount,
    formatDebtRow
      "Dependent eliminator motive (fixed-motive recursors)"
      motiveDebtCount,
    formatDebtRow
      "Unit-typed proof placeholders (Ty.unit obligations)"
      unitPlaceholderDebtCount,
    formatDebtRow
      "Modal no-op (modIntro/Elim/subsume w/o Ty.modal)"
      modalNoopDebtCount,
    formatDebtRow
      "Session no-advance (no protocol continuation)"
      sessionNoAdvanceDebtCount,
    formatDebtRow
      "Equiv coherence (equivIntroHet w/o leftInv/rightInv)"
      equivCoherenceDebtCount,
    formatDebtRow
      "Ty raw endpoint (Ty.id/path/oeq w/o typed endpoints)"
      tyRawEndpointDebtCount,
    formatDebtRow
      "Ty unstructured schema (modal/session/effect raw tag)"
      tyUnstructuredSchemaDebtCount,
    formatDebtRow
      "Transport linkage (transp w/o typed endpoint linkage)"
      transportLinkageDebtCount,
    formatDebtRow
      "Glue schema (glueIntro w/o boundary cofibration)"
      glueSchemaDebtCount,
    formatDebtRow
      "Effect schema (effectPerform w/o effect row)"
      effectSchemaDebtCount,
    formatDebtRow
      "Session schema (session w/o SessionProtocol)"
      sessionSchemaDebtCount,
    formatDebtRow
      "Hcomp Kan (hcomp w/o boundary cofibration)"
      hcompKanDebtCount,
    "  ──────────────────────────────────────────────────────────",
    "  COVERAGE MATRICES  (rich Term ctor → mirror declarations)",
    s!"    Bridge encoding (FX1.encodeTermSound_*):     " ++
      s!"{bridgeCoveredCount}/{totalCtorCount} " ++
      s!"({totalCtorCount - bridgeCoveredCount} unbridged)",
    s!"    Step.par cong (Step.par.*Cong):              " ++
      s!"{stepParCongCoveredCount}/{totalCtorCount} " ++
      s!"({totalCtorCount - stepParCongCoveredCount} uncovered)",
    s!"    Conv cong (Conv.*Cong / Conv.*_cong):        " ++
      s!"{convCongCoveredCount}/{totalCtorCount} " ++
      s!"({totalCtorCount - convCongCoveredCount} uncovered)",
    s!"    toRaw projection (Term.toRaw_*):             " ++
      s!"{toRawCoveredCount}/{totalCtorCount} " ++
      s!"({totalCtorCount - toRawCoveredCount} uncovered)",
    s!"    IsClosedTy parity (scope-indep Ty → IsClosedTy):  " ++
      s!"{isClosedTyParityUncoveredCount} gaps",
    "  ──────────────────────────────────────────────────────────",
    "  INDUCTIVE CTOR-COUNT SNAPSHOTS  (regression-prevention)",
    s!"    Term:        {termCtorCount}",
    s!"    Ty:          {tyCtorCount}",
    s!"    Step:        {stepCtorCount}",
    s!"    Step.par:    {stepParCtorCount}",
    s!"    RawTerm:     {rawTermCtorCount}",
    "  ──────────────────────────────────────────────────────────",
    "  REFL-FRAGMENT DEPENDENCY CENSUS",
    s!"    Headline names backed by manufactured rules:  " ++
      s!"{headlineReflFragmentCount}",
    s!"    Broad non-allowlisted dependents (wrappers):  " ++
      s!"{broadManufacturedDependentCount}",
    "  ──────────────────────────────────────────────────────────",
    "  KERNEL DECL-SHAPE CENSUS  (axiom-adjacent constructs)",
    s!"    Cast-operator dependents " ++
      "(Eq.mpr/Eq.ndrec/Eq.rec/HEq.*/cast):" ++
      s!" {castOperatorDependentCount}",
    s!"    Forbidden shapes (partial/opaque/unsafe):    " ++
      s!"{forbiddenShapeCount}",
    s!"    Single-step Conv claims (Conv.fromStep wraps): " ++
      s!"{singleStepConvClaimCount}",
    s!"    All-raw-payload Term ctors (untyped wrappers): " ++
      s!"{allRawPayloadCount}",
    s!"    Step.par cong rules w/o full Compat coverage:  " ++
      s!"{reductionCompatUncoveredCount}",
    "  ──────────────────────────────────────────────────────────",
    "  AXIOM-ADJACENT DEPENDENCY CENSUS",
    s!"    Inhabited / Nonempty / Classical.choice deps:  " ++
      s!"{inhabitedDependentCount}",
    s!"    HEq result-type theorems:                      " ++
      s!"{heqResultTypeCount}",
    s!"    Decidable.decide / Decidable.em deps:          " ++
      s!"{decideDependentCount}",
    s!"    Subsingleton.elim deps:                        " ++
      s!"{subsingletonDependentCount}",
    s!"    Match-compiler equation lemmas in kernel:      " ++
      s!"{matchCompilerEquationCount}",
    s!"    Suspicious rfl-only on non-trivial names:      " ++
      s!"{rflOnNonTrivialNameCount}",
    s!"    Universe-polymorphic kernel decls:             " ++
      s!"{universePolymorphicCount}",
    s!"    Quot / Quotient family deps:                   " ++
      s!"{quotDependentCount}",
    s!"    Acc / WellFounded family deps:                 " ++
      s!"{accDependentCount}",
    s!"    Lean.Elab/Meta/Parser deps in production:      " ++
      s!"{leanMetaDependentCount}",
    "  ──────────────────────────────────────────────────────────",
    "  LEAN-TRUST-ESCAPE / DECL-SHAPE CENSUS (this batch)",
    s!"    Coe / CoeSort / CoeFun deps:                   " ++
      s!"{coeDependentCount}",
    s!"    OfNat / OfScientific deps:                     " ++
      s!"{ofNatDependentCount}",
    s!"    Subtype.mk / Subtype.val deps:                 " ++
      s!"{subtypeDependentCount}",
    s!"    Function.Injective/Bijective/Surjective deps:  " ++
      s!"{functionPropertyDependentCount}",
    s!"    Eq.symm/trans/mp/recOn/subst deps:             " ++
      s!"{eqRewritingDependentCount}",
    s!"    Reducible / abbrev kernel decls:               " ++
      s!"{reducibleDeclCount}",
    s!"    False-in-result-type kernel decls:             " ++
      s!"{falseResultTypeCount}",
    s!"    Sigma / PSigma / Sum / PSum / PProd deps:      " ++
      s!"{dependentPairDependentCount}",
    s!"    Classical.choose/em/byContradiction deps:      " ++
      s!"{classicalReasoningDependentCount}",
    s!"    Hashable / Repr / ToString / BEq deps:         " ++
      s!"{apiTypeclassDependentCount}",
    s!"    IO / Task / EIO effect deps:                   " ++
      s!"{ioEffectDependentCount}",
    s!"    And/Or/Iff/Prod anonymous-projection deps:     " ++
      s!"{anonymousProjectionDependentCount}",
    bannerEdge,
    "  Notes:",
    "    * All counts read live from current environment.",
    "    * Build-failing budgets fire EARLIER if any number rose; " ++
      "a rendered",
    "      dashboard means every ratchet held this build.",
    "    * Lower is better.  Each shipped fix should reduce one row.",
    bannerEdge
  ]
  logInfo (String.intercalate "\n" dashLines)

end LeanFX2.Tools
