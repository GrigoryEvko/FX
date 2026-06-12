import FX1Poly.Core.EtaIotaCoreReplacement
import FX1Poly.Core.StepEtaOverTable
import FX1Poly.Core.StrongNormalizationUnion

/-! # EtaIotaRootCommutation — ETA-T5 increment 3: the root-eta case
of the quasi-commutation

A root table eta contraction followed by ANY iota step reorders into
one iota step followed by a union-star reduction:

    introCell --eta--> core --iota--> target

becomes

    introCell --iota--> introCell[first copy stepped]
              --iota*--> introCell[all copies stepped]
              --eta--> target.

The intro cell holds the (weakened) core once per observation; the
replacement chain steps each copy (`extractCoreFrom?_replaceCore`),
sibling observations survive because a well-formed row watches
pairwise-distinct intro slots, and the fully-replaced cell re-contracts
to the TARGET (`contractsOn?_ofExtracts`).  This generalizes the five
bespoke per-constructor postponement lemmas (`EtaPostponementOverBeta`)
to EVERY row of any well-formed scope-safe table — including the
duplicating rows (etaPair-style), whose extra copies ride in the
union-star tail exactly as Klop-style duplication requires.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaRootCommutation.lean`. -/

namespace FX1Poly.Core

/-! ## Star prepend and the spine star -/

/-- Prepend a left step to a union star. -/
theorem UnionStar.headLeft {Alpha : Type}
    {reduceLeft reduceRight : Alpha → Alpha → Prop} {a b c : Alpha}
    (firstStep : reduceLeft a b)
    (restStar : UnionStar reduceLeft reduceRight b c) :
    UnionStar reduceLeft reduceRight a c := by
  induction restStar with
  | refl => exact .tailLeft (.refl _) firstStep
  | tailLeft _ stepToReduct ih => exact .tailLeft ih stepToReduct
  | tailRight _ stepToReduct ih => exact .tailRight ih stepToReduct

/-- Head-oriented reflexive-transitive closure of spine steps — the
shape the replacement chain produces. -/
inductive StepOverTableChildrenStar (table : List IotaRuleDesc) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | refl {parentScope : Nat} {binderShifts : List Nat}
      (children : RawTermChildren binderShifts parentScope) :
      StepOverTableChildrenStar table children children
  | head {parentScope : Nat} {binderShifts : List Nat}
      {children middleChildren children' :
        RawTermChildren binderShifts parentScope}
      (firstStep : StepOverTableChildren table children middleChildren)
      (restStar :
        StepOverTableChildrenStar table middleChildren children') :
      StepOverTableChildrenStar table children children'

/-- A spine star lifts to a union star of parent-cell congruences. -/
theorem unionStarCongOfChildrenStar {iotaTable : List IotaRuleDesc}
    {etaTable : List EtaRuleDesc}
    {scope : Nat} (gen : Generator) (payload : gen.payload scope)
    {children children' : RawTermChildren gen.binderShifts scope}
    (childrenStar :
      StepOverTableChildrenStar iotaTable children children') :
    UnionStar (StepOverTable iotaTable (scope := scope))
      (StepEtaOverTable etaTable)
      (.mkGen gen payload children) (.mkGen gen payload children') := by
  induction childrenStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact UnionStar.headLeft
        (StepOverTable.cong gen payload firstStep) ih

/-! ## Agreement-gate extraction and re-assembly -/

/-- Every spec behind a passing agreement gate extracts the shared
core. -/
theorem etaObservationsAgree_memberExtracts {scope : Nat}
    {introShifts : List Nat}
    {introChildren : RawTermChildren introShifts scope}
    {core : RawTerm scope} :
    (specs : List EtaObservationSpec) →
    etaObservationsAgree introChildren core specs = true →
    {spec : EtaObservationSpec} → spec ∈ specs →
    spec.extractCoreFrom? introChildren = some core
  | [], _, _, isMember => by cases isMember
  | spec :: restSpecs, agree, querySpec, isMember => by
      dsimp only [etaObservationsAgree] at agree
      match extractEq : spec.extractCoreFrom? introChildren with
      | none =>
          rw [extractEq] at agree
          exact nomatch agree
      | some otherCore =>
          rw [extractEq] at agree
          have agreeReduced :
              ((if otherCore = core then true else false)
                && etaObservationsAgree introChildren core restSpecs)
              = true := agree
          by_cases coresAgree : otherCore = core
          case neg =>
              rw [if_neg coresAgree] at agreeReduced
              exact nomatch agreeReduced
          case pos =>
              obtain ⟨_, restAgree⟩ := andEqTrueSplit agreeReduced
              cases isMember with
              | head => exact extractEq.trans (congrArg some coresAgree)
              | tail _ isInRest =>
                  exact etaObservationsAgree_memberExtracts restSpecs
                    restAgree isInRest

/-- All specs extracting the shared core pass the agreement gate. -/
theorem etaObservationsAgree_ofAllExtract {scope : Nat}
    {introShifts : List Nat}
    {introChildren : RawTermChildren introShifts scope}
    {core : RawTerm scope} :
    (specs : List EtaObservationSpec) →
    (∀ spec, spec ∈ specs →
      spec.extractCoreFrom? introChildren = some core) →
    etaObservationsAgree introChildren core specs = true
  | [], _ => rfl
  | spec :: restSpecs, allExtract => by
      dsimp only [etaObservationsAgree]
      rw [allExtract spec (.head _)]
      show ((if core = core then true else false)
          && etaObservationsAgree introChildren core restSpecs)
        = true
      rw [if_pos rfl,
        etaObservationsAgree_ofAllExtract restSpecs
          (fun innerSpec isInRest =>
            allExtract innerSpec (.tail _ isInRest))]
      rfl

/-- The richer contraction inversion: the primary extract AND the
agreement gate of the rest. -/
theorem EtaRuleDesc.contractsOn?_consInversion (rule : EtaRuleDesc)
    {scope : Nat}
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    (contracts : rule.contractsOn? introChildren = some core) :
    ∃ (primarySpec : EtaObservationSpec)
      (restSpecs : List EtaObservationSpec),
      rule.observations = primarySpec :: restSpecs
      ∧ primarySpec.extractCoreFrom? introChildren = some core
      ∧ etaObservationsAgree introChildren core restSpecs = true := by
  dsimp only [EtaRuleDesc.contractsOn?] at contracts
  match specsEq : rule.observations with
  | [] =>
      rw [specsEq] at contracts
      exact nomatch contracts
  | primarySpec :: restSpecs =>
      rw [specsEq] at contracts
      have contractsReduced :
          (primarySpec.extractCoreFrom? introChildren).bind
              (fun sharedCore =>
                if etaObservationsAgree introChildren sharedCore
                    restSpecs then some sharedCore
                else none)
            = some core := contracts
      match extractEq : primarySpec.extractCoreFrom? introChildren with
      | none =>
          rw [extractEq] at contractsReduced
          exact nomatch contractsReduced
      | some extractedCore =>
          rw [extractEq] at contractsReduced
          have gateReduced :
              (if etaObservationsAgree introChildren extractedCore
                  restSpecs then some extractedCore
              else none)
                = some core := contractsReduced
          by_cases agreeHolds :
              etaObservationsAgree introChildren extractedCore restSpecs
                = true
          case neg =>
              rw [if_neg agreeHolds] at gateReduced
              exact nomatch gateReduced
          case pos =>
              rw [if_pos agreeHolds] at gateReduced
              have coreIsExtracted : extractedCore = core :=
                Option.some.inj gateReduced
              rw [coreIsExtracted] at agreeHolds
              exact ⟨primarySpec, restSpecs, rfl,
                extractEq.trans (congrArg some coreIsExtracted),
                agreeHolds⟩

/-- Re-assemble a contraction from per-observation extracts. -/
theorem EtaRuleDesc.contractsOn?_ofExtracts (rule : EtaRuleDesc)
    {scope : Nat}
    {introChildren :
      RawTermChildren rule.introGenerator.binderShifts scope}
    {core : RawTerm scope}
    {primarySpec : EtaObservationSpec}
    {restSpecs : List EtaObservationSpec}
    (specsShape : rule.observations = primarySpec :: restSpecs)
    (primaryExtracts :
      primarySpec.extractCoreFrom? introChildren = some core)
    (restAgree :
      etaObservationsAgree introChildren core restSpecs = true) :
    rule.contractsOn? introChildren = some core := by
  dsimp only [EtaRuleDesc.contractsOn?]
  rw [specsShape]
  show (primarySpec.extractCoreFrom? introChildren).bind
      (fun sharedCore =>
        if etaObservationsAgree introChildren sharedCore restSpecs then
          some sharedCore
        else none)
    = some core
  rw [primaryExtracts]
  show (if etaObservationsAgree introChildren core restSpecs then
      some core
    else none)
    = some core
  rw [if_pos restAgree]

/-! ## The replacement chain -/

/-- **The chain**: one iota step on the shared core replaces, one
observation at a time, every copy inside the intro spine; the
pairwise-distinct slots keep siblings intact, so afterwards EVERY
observation extracts the target.  Slots outside the observation set
are untouched. -/
theorem replaceCoresAlongObservations
    {iotaTable : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    {scope : Nat} {introShifts : List Nat}
    {core target : RawTerm scope}
    (iotaStep : StepOverTable iotaTable core target) :
    (specs : List EtaObservationSpec) →
    (specsAreScopeSafe : ∀ spec, spec ∈ specs → spec.IsScopeSafe) →
    (specsAreDistinct : rowObservationSlotsDistinct specs = true) →
    {introChildren : RawTermChildren introShifts scope} →
    (allExtract : ∀ spec, spec ∈ specs →
      spec.extractCoreFrom? introChildren = some core) →
    ∃ replacedChildren : RawTermChildren introShifts scope,
      StepOverTableChildrenStar iotaTable introChildren replacedChildren
      ∧ (∀ spec, spec ∈ specs →
          spec.extractCoreFrom? replacedChildren = some target)
      ∧ (∀ otherSlot otherShift : Nat,
          (∀ spec, spec ∈ specs → otherSlot ≠ spec.introChildSlot) →
          replacedChildren.childAtShift? otherSlot otherShift
            = introChildren.childAtShift? otherSlot otherShift)
  | [], _, _, introChildren, _ => by
      refine ⟨introChildren, .refl introChildren, ?_, ?_⟩
      · intro _querySpec isMember
        cases isMember
      · intro _otherSlot _otherShift _avoidsAll
        rfl
  | spec :: restSpecs, specsAreScopeSafe, specsAreDistinct,
      introChildren, allExtract => by
      dsimp only [rowObservationSlotsDistinct] at specsAreDistinct
      obtain ⟨headDiffers, restDistinct⟩ :=
        andEqTrueSplit specsAreDistinct
      have headSlotAvoidsRest :
          ∀ restSpec, restSpec ∈ restSpecs →
          spec.introChildSlot ≠ restSpec.introChildSlot := by
        intro restSpec isInRest slotsCollide
        have differs := listForall_mem restSpecs headDiffers isInRest
        dsimp only [observationSlotsDiffer] at differs
        rw [if_pos slotsCollide] at differs
        exact Bool.noConfusion differs
      obtain ⟨steppedChildren, firstStep, headExtractsTarget,
          firstPreserved⟩ :=
        EtaObservationSpec.extractCoreFrom?_replaceCore tableIsUniform
          spec (specsAreScopeSafe spec (.head _))
          (allExtract spec (.head _)) iotaStep
      have restExtractStepped :
          ∀ restSpec, restSpec ∈ restSpecs →
          restSpec.extractCoreFrom? steppedChildren = some core := by
        intro restSpec isInRest
        rw [restSpec.extractCoreFrom?_congrLookup
          (firstPreserved restSpec.introChildSlot restSpec.binderDepth
            (fun slotsCollide =>
              headSlotAvoidsRest restSpec isInRest slotsCollide.symm))]
        exact allExtract restSpec (.tail _ isInRest)
      obtain ⟨replacedChildren, restStar, restExtractReplaced,
          restPreserved⟩ :=
        replaceCoresAlongObservations tableIsUniform iotaStep restSpecs
          (fun innerSpec isInRest =>
            specsAreScopeSafe innerSpec (.tail _ isInRest))
          restDistinct restExtractStepped
      have headExtractReplaced :
          spec.extractCoreFrom? replacedChildren = some target := by
        rw [spec.extractCoreFrom?_congrLookup
          (restPreserved spec.introChildSlot spec.binderDepth
            headSlotAvoidsRest)]
        exact headExtractsTarget
      refine ⟨replacedChildren, .head firstStep restStar, ?_, ?_⟩
      · intro querySpec isMember
        cases isMember with
        | head => exact headExtractReplaced
        | tail _ isInRest => exact restExtractReplaced querySpec isInRest
      · intro otherSlot otherShift avoidsAll
        rw [restPreserved otherSlot otherShift
            (fun innerSpec isInRest =>
              avoidsAll innerSpec (.tail _ isInRest)),
          firstPreserved otherSlot otherShift
            (avoidsAll spec (.head _))]

/-! ## ★ The root-eta case of the quasi-commutation -/

/-- **Root eta quasi-commutes over iota, generically**: a root table
eta contraction followed by any iota step reorders into ONE iota step
(the first copy replacement) followed by a union-star reduction (the
remaining copy replacements, then one root eta contraction to the
target).  The table generalization of all five bespoke postponement
lemmas — every future row inherits it from its well-formedness and
scope-safety certificates. -/
theorem etaRedexQuasiCommutesOverIota
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
          (StepEtaOverTable etaTable) commonReduct target := by
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
  -- the fronted single iota step: replace the primary's copy
  obtain ⟨steppedChildren, firstStep, primaryExtractsTarget,
      firstPreserved⟩ :=
    EtaObservationSpec.extractCoreFrom?_replaceCore tableIsUniform
      primarySpec
      (ruleIsSafe.observationsAreScopeSafe primarySpec
        (by rw [specsShape]; exact List.Mem.head _))
      primaryExtracts iotaStep
  -- the rest still extract the core on the stepped spine
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
  -- chain through the remaining observations
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
  -- the fully-replaced cell contracts to the target
  have contractsTarget :
      rule.contractsOn? replacedChildren = some target :=
    rule.contractsOn?_ofExtracts specsShape primaryExtractReplaced
      (etaObservationsAgree_ofAllExtract restSpecs restExtractReplaced)
  refine ⟨.mkGen rule.introGenerator introPayload steppedChildren,
    StepOverTable.cong rule.introGenerator introPayload firstStep, ?_⟩
  exact UnionStar.tailRight
    (unionStarCongOfChildrenStar rule.introGenerator introPayload
      restStar)
    (StepEtaOverTable.etaRedex isRow isRawTier introPayload
      contractsTarget)

end FX1Poly.Core
