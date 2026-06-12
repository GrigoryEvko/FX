import FX1Poly.Core.EtaIotaRootCommutation
import FX1Poly.Core.StepEtaRootTable
import FX1Poly.Core.StrongNormalizationEtaTable

/-! # EtaIotaRootTierUnion — ETA-T6 increment 6a: union SN for table
iota plus ROOT table eta

At the root tier the GLOBAL Geser criterion is satisfiable: the
copy-replacement argument (`etaRedexQuasiCommutesOverIota`) is the
whole quasi-commutation — root eta cannot bury a redex at a scrutinee
slot, so the cross-pair refutations cannot arise.  The shipped
quadrant-1 residual is, BY CONSTRUCTION, iota spine steps capped by
one root contraction; this module restates it with that shape in the
TYPE (the right relation is `StepEtaRootOverTable`), packages the
`QuasiCommutesRightOverLeft` hypothesis, inherits the right SN from
the ETA-T3 schema theorem by subrelation, and instantiates the global
`accUnion`: iota accessibility at a term gives union accessibility,
for ANY uniform iota table against any wf, scope-safe eta table.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaRootTierUnion.lean`. -/

namespace FX1Poly.Core

/-- A left-only spine star lifts to a union star against ANY right
relation (the shipped lift hardcodes the full table eta on the right;
the steps emitted are left congruences either way). -/
theorem unionStarCongOfChildrenStarRight {iotaTable : List IotaRuleDesc}
    {scope : Nat} (reduceRight : RawTerm scope → RawTerm scope → Prop)
    (gen : Generator) (payload : gen.payload scope)
    {children children' : RawTermChildren gen.binderShifts scope}
    (childrenStar :
      StepOverTableChildrenStar iotaTable children children') :
    UnionStar (StepOverTable iotaTable (scope := scope)) reduceRight
      (.mkGen gen payload children) (.mkGen gen payload children') := by
  induction childrenStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact UnionStar.headLeft
        (StepOverTable.cong gen payload firstStep) ih

/-- ★ **Quadrant 1 at the root tier**: a root eta contraction followed
by an iota step reorders into one fronted iota step and a union star
whose right steps are ROOT contractions — the shipped copy-replacement
argument with its actual residual shape in the type. -/
theorem etaRedexQuasiCommutesOverIotaRoot
    {iotaTable : List IotaRuleDesc} {etaTable : List EtaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {rule : EtaRuleDesc} (isRow : rule ∈ etaTable)
    (isRawTier : rule.requiresTypedFiring = false)
    {scope : Nat}
    (introPayload : rule.introGenerator.payload scope)
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope}
    {core target : RawTerm scope}
    (contracts : rule.contractsOn? introChildren = some core)
    (iotaStep : StepOverTable iotaTable core target) :
    ∃ commonReduct : RawTerm scope,
      StepOverTable iotaTable
        (.mkGen rule.introGenerator introPayload introChildren)
        commonReduct
      ∧ UnionStar (StepOverTable iotaTable (scope := scope))
          (StepEtaRootOverTable etaTable) commonReduct target := by
  obtain ⟨primarySpec, restSpecs, specsShape, primaryExtracts,
      restAgree⟩ :=
    rule.contractsOn?_consInversion contracts
  have ruleIsSafe := rowsAreScopeSafe rule isRow
  have rowDistinct :
      rowObservationSlotsDistinct rule.observations = true :=
    listForall_mem etaTable etaTableIsWf.observationSlotsAreDistinct
      isRow
  rw [specsShape] at rowDistinct
  dsimp only [rowObservationSlotsDistinct] at rowDistinct
  obtain ⟨headDiffers, restDistinct⟩ := andEqTrueSplit rowDistinct
  have headSlotAvoidsRest :
      ∀ restSpec, restSpec ∈ restSpecs →
      primarySpec.introChildSlot ≠ restSpec.introChildSlot := by
    intro restSpec isInRest slotsCollide
    have differs := listForall_mem restSpecs headDiffers isInRest
    dsimp only [observationSlotsDiffer] at differs
    rw [if_pos slotsCollide] at differs
    exact Bool.noConfusion differs
  obtain ⟨steppedChildren, firstStep, primaryExtractsTarget,
      firstPreserved⟩ :=
    EtaObservationSpec.extractCoreFrom?_replaceCore tableIsUniform
      primarySpec
      (ruleIsSafe.observationsAreScopeSafe primarySpec
        (by rw [specsShape]; exact List.Mem.head _))
      primaryExtracts iotaStep
  have restExtractStepped :
      ∀ restSpec, restSpec ∈ restSpecs →
      restSpec.extractCoreFrom? steppedChildren = some core := by
    intro restSpec isInRest
    rw [restSpec.extractCoreFrom?_congrLookup
      (firstPreserved restSpec.introChildSlot restSpec.binderDepth
        (fun slotsCollide =>
          headSlotAvoidsRest restSpec isInRest slotsCollide.symm))]
    exact etaObservationsAgree_memberExtracts restSpecs restAgree
      isInRest
  obtain ⟨replacedChildren, restStar, restExtractReplaced,
      restPreserved⟩ :=
    replaceCoresAlongObservations tableIsUniform iotaStep restSpecs
      (fun innerSpec isInRest =>
        ruleIsSafe.observationsAreScopeSafe innerSpec
          (by rw [specsShape]; exact List.Mem.tail _ isInRest))
      restDistinct restExtractStepped
  have primaryExtractReplaced :
      primarySpec.extractCoreFrom? replacedChildren = some target := by
    rw [primarySpec.extractCoreFrom?_congrLookup
      (restPreserved primarySpec.introChildSlot primarySpec.binderDepth
        headSlotAvoidsRest)]
    exact primaryExtractsTarget
  have contractsTarget :
      rule.contractsOn? replacedChildren = some target :=
    rule.contractsOn?_ofExtracts specsShape primaryExtractReplaced
      (etaObservationsAgree_ofAllExtract restSpecs restExtractReplaced)
  refine ⟨.mkGen rule.introGenerator introPayload steppedChildren,
    StepOverTable.cong rule.introGenerator introPayload firstStep, ?_⟩
  exact UnionStar.tailRight
    (unionStarCongOfChildrenStarRight
      (StepEtaRootOverTable etaTable) rule.introGenerator introPayload
      restStar)
    (StepEtaRootOverTable.etaRedex isRow isRawTier introPayload
      contractsTarget)

/-- ★★ **The Geser hypothesis at the root tier, GLOBAL**: root table
eta quasi-commutes over table iota everywhere — no typing, no oracle
(root eta cannot reach the cross-pair configurations). -/
theorem quasiCommutesRootEtaOverIota
    {iotaTable : List IotaRuleDesc} {etaTable : List EtaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    (scope : Nat) :
    QuasiCommutesRightOverLeft
      (StepOverTable iotaTable (scope := scope))
      (StepEtaRootOverTable etaTable) := by
  intro source middleTerm target rootStep iotaStep
  cases rootStep with
  | etaRedex isRow isRawTier introPayload contracts =>
      exact etaRedexQuasiCommutesOverIotaRoot tableIsUniform
        etaTableIsWf rowsAreScopeSafe isRow isRawTier introPayload
        contracts iotaStep

/-- Root table eta is strongly normalizing — a subrelation of the
ETA-T3 schema SN. -/
theorem stepEtaRootOverTable_isStronglyNormalizing
    (etaTable : List EtaRuleDesc) {scope : Nat}
    (sourceTerm : RawTerm scope) :
    Acc (fun laterTerm earlierTerm =>
      StepEtaRootOverTable etaTable earlierTerm laterTerm)
      sourceTerm :=
  Subrelation.wf
    (fun rootStep => rootStep.toStepEtaOverTable)
    (stepEtaOverTable_wellFounded etaTable)
    |>.apply sourceTerm

/-- ★★ **Union SN at the root tier**: iota accessibility at a term
gives accessibility for the iota∪root-eta union — the GLOBAL Geser
engine, no typing, no oracle. -/
theorem accUnionTablesRootEta
    {iotaTable : List IotaRuleDesc} {etaTable : List EtaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    (etaTableIsWf : WfEtaTable etaTable iotaTable)
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} {subject : RawTerm scope}
    (iotaAccessible :
      Acc (fun laterTerm earlierTerm =>
        StepOverTable iotaTable earlierTerm laterTerm) subject) :
    Acc (UnionSuccessor
      (StepOverTable iotaTable (scope := scope))
      (StepEtaRootOverTable etaTable)) subject :=
  accUnion
    (fun term =>
      stepEtaRootOverTable_isStronglyNormalizing etaTable term)
    (quasiCommutesRootEtaOverIota tableIsUniform etaTableIsWf
      rowsAreScopeSafe scope)
    iotaAccessible

end FX1Poly.Core
