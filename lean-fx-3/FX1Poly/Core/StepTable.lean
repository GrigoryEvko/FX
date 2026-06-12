import FX1Poly.Core.Step
import FX1Poly.Core.StepOverTable
import FX1Poly.Core.TableFireRoot
import FX1Poly.Core.HeadStep
import FX1Poly.Core.IotaHeadStep
import FX1Poly.Core.WeakHeadStepSubsumes

/-! # FX1Poly/Core/StepTable — the Step <-> table ADEQUACY layer (IOTA-T1)

The relation itself (`StepOverTable`, `StepTable`, monotonicity, the
firing-inversion trio) lives in `StepOverTable.lean` — bespoke-free.
This file proves the two-way adequacy against the bespoke `Step`:

  * FORWARD (`Step.toLegacyTableStep`): each bespoke `Step` root
    constructor maps to its row firing BY `rfl` — the IOTA-T0 adequacy
    equations compute the firing on every redex shape.
  * BACKWARD (`StepOverTable.legacyToStep`): a root firing of a legacy
    row yields the bespoke constructor.  The generic inversion trio
    extracts the constructor head POSITIVELY from the firing
    hypothesis, so the 17 per-row inversions are head-substitution +
    spine casing + `Option.some.inj` — no per-row case analysis on
    generators.
  * `stepOverLegacyTable_iff_step` — the headline: the legacy-table
    relation IS `Step`.
  * `Step.toStepTable` — the canonical embedding into the full table
    via monotonicity.

This file is bespoke-iota SEDIMENT BY DESIGN: it mentions every bespoke
iota Step constructor (that is its content), and it is the LAST file
scheduled to go when IOTA-T11 deletes the bespoke ctors — the adequacy
becomes vacuous once `Step` loses its iota arms.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditStepTable.lean`. -/

namespace FX1Poly.Core

/-! ## FORWARD adequacy: every bespoke Step is a legacy-table step

Each root arm is the row firing BY `rfl` — the IOTA-T0 adequacy
equations compute `firesOn?` on every redex shape. -/

mutual

/-- `Step ⊆ StepOverTable legacyIotaRuleTable` — the forward half of
the IOTA-T1 adequacy.  Each bespoke root constructor maps to a
`tableRedex` whose firing equation closes definitionally. -/
theorem Step.toLegacyTableStep {scope : Nat} {source target : RawTerm scope} :
    Step source target → StepOverTable legacyIotaRuleTable source target
  | .beta => .tableRedex betaIotaRow_memLegacy () rfl
  | .cong gen payload childStep =>
      .cong gen payload (StepChildren.toLegacyTableStepChildren childStep)
  | .iotaBoolTrue => .tableRedex boolTrueIotaRow_memLegacy () rfl
  | .iotaBoolFalse => .tableRedex boolFalseIotaRow_memLegacy () rfl
  | .iotaFstPair => .tableRedex fstPairIotaRow_memLegacy () rfl
  | .iotaSndPair => .tableRedex sndPairIotaRow_memLegacy () rfl
  | .iotaNatElimZero => .tableRedex natElimZeroIotaRow_memLegacy () rfl
  | .iotaNatRecZero => .tableRedex natRecZeroIotaRow_memLegacy () rfl
  | .iotaListElimNil => .tableRedex listElimNilIotaRow_memLegacy () rfl
  | .iotaOptionMatchNone => .tableRedex optionMatchNoneIotaRow_memLegacy () rfl
  | .iotaOptionMatchSome => .tableRedex optionMatchSomeIotaRow_memLegacy () rfl
  | .iotaEitherMatchInl => .tableRedex eitherMatchInlIotaRow_memLegacy () rfl
  | .iotaEitherMatchInr => .tableRedex eitherMatchInrIotaRow_memLegacy () rfl
  | .iotaNatElimSucc => .tableRedex natElimSuccIotaRow_memLegacy () rfl
  | .iotaNatRecSucc => .tableRedex natRecSuccIotaRow_memLegacy () rfl
  | .iotaListElimCons => .tableRedex listElimConsIotaRow_memLegacy () rfl
  | .iotaIdJRefl => .tableRedex idJReflIotaRow_memLegacy () rfl
  | .iotaIdStrictRecRefl => .tableRedex idStrictRecReflIotaRow_memLegacy () rfl

/-- Spine companion of `Step.toLegacyTableStep`. -/
theorem StepChildren.toLegacyTableStepChildren {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope} :
    StepChildren children children' →
    StepOverTableChildren legacyIotaRuleTable children children'
  | .here rest childStep => .here rest (Step.toLegacyTableStep childStep)
  | .there head restStep =>
      .there head (StepChildren.toLegacyTableStepChildren restStep)

end

/-! ## BACKWARD adequacy: each legacy row's firing is the bespoke Step

17 per-row root inversions: case the spine into its concrete children,
extract the constructor head POSITIVELY from the firing, substitute,
case the scrutinee's children — at which point the firing equation
computes and `Option.some.inj` delivers the reduct identification. -/

theorem betaRowFiringToHeadStep {scope : Nat}
    (elimPayload : betaIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren betaIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : betaIotaRow.firesOn? elimPayload spine = some reduct) :
    HeadStep (.mkGen betaIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons functionChild restSpine =>
    cases restSpine with
    | childCons argumentChild restNil =>
      cases restNil
      cases functionChild with
      | mkGen functionGenerator functionPayload functionChildren =>
        intro fires
        have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
        subst isHead
        cases functionChildren with
        | childCons domainAnn lamRest =>
          cases lamRest with
          | childCons lamBody lamNil =>
            cases lamNil
            exact Option.some.inj fires ▸ HeadStep.beta

/-- The beta row's firing as the bespoke `Step` — the head-step
inversion pushed through the funnel (kept for the typed-link
consumers). -/
theorem betaRowFiringToStep {scope : Nat}
    (elimPayload : betaIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren betaIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : betaIotaRow.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen betaIotaRow.elimGenerator elimPayload spine) reduct :=
  (betaRowFiringToHeadStep elimPayload fires).toStep

theorem boolTrueRowFiringToIotaHead {scope : Nat}
    (elimPayload : boolTrueIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren boolTrueIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : boolTrueIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen boolTrueIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons thenBranch restTwo =>
      cases restTwo with
      | childCons elseBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ IotaHeadStep.iotaBoolTrue

theorem boolFalseRowFiringToIotaHead {scope : Nat}
    (elimPayload : boolFalseIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren boolFalseIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : boolFalseIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen boolFalseIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons thenBranch restTwo =>
      cases restTwo with
      | childCons elseBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ IotaHeadStep.iotaBoolFalse

theorem fstPairRowFiringToIotaHead {scope : Nat}
    (elimPayload : fstPairIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren fstPairIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : fstPairIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen fstPairIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons scrutineeChild restNil =>
    cases restNil
    cases scrutineeChild with
    | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      intro fires
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases scrutineeChildren with
      | childCons firstValue pairRest =>
        cases pairRest with
        | childCons secondValue pairNil =>
          cases pairNil
          exact Option.some.inj fires ▸ IotaHeadStep.iotaFstPair

theorem sndPairRowFiringToIotaHead {scope : Nat}
    (elimPayload : sndPairIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren sndPairIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : sndPairIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen sndPairIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons scrutineeChild restNil =>
    cases restNil
    cases scrutineeChild with
    | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      intro fires
      have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
      subst isHead
      cases scrutineeChildren with
      | childCons firstValue pairRest =>
        cases pairRest with
        | childCons secondValue pairNil =>
          cases pairNil
          exact Option.some.inj fires ▸ IotaHeadStep.iotaSndPair

theorem natElimZeroRowFiringToIotaHead {scope : Nat}
    (elimPayload : natElimZeroIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natElimZeroIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natElimZeroIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen natElimZeroIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ IotaHeadStep.iotaNatElimZero

theorem natRecZeroRowFiringToIotaHead {scope : Nat}
    (elimPayload : natRecZeroIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natRecZeroIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natRecZeroIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen natRecZeroIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ IotaHeadStep.iotaNatRecZero

theorem natElimSuccRowFiringToIotaHead {scope : Nat}
    (elimPayload : natElimSuccIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natElimSuccIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natElimSuccIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen natElimSuccIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons predecessor succNil =>
              cases succNil
              exact Option.some.inj fires ▸ IotaHeadStep.iotaNatElimSucc

theorem natRecSuccRowFiringToIotaHead {scope : Nat}
    (elimPayload : natRecSuccIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren natRecSuccIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : natRecSuccIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen natRecSuccIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons zeroBranch restTwo =>
      cases restTwo with
      | childCons succBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons predecessor succNil =>
              cases succNil
              exact Option.some.inj fires ▸ IotaHeadStep.iotaNatRecSucc

theorem listElimNilRowFiringToIotaHead {scope : Nat}
    (elimPayload : listElimNilIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren listElimNilIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : listElimNilIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen listElimNilIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons nilBranch restTwo =>
      cases restTwo with
      | childCons consBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ IotaHeadStep.iotaListElimNil

theorem listElimConsRowFiringToIotaHead {scope : Nat}
    (elimPayload : listElimConsIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren listElimConsIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : listElimConsIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen listElimConsIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons nilBranch restTwo =>
      cases restTwo with
      | childCons consBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons headValue consRest =>
              cases consRest with
              | childCons tailValue consNil =>
                cases consNil
                exact Option.some.inj fires ▸ IotaHeadStep.iotaListElimCons

theorem optionMatchNoneRowFiringToIotaHead {scope : Nat}
    (elimPayload : optionMatchNoneIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren optionMatchNoneIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : optionMatchNoneIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen optionMatchNoneIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons noneBranch restTwo =>
      cases restTwo with
      | childCons someBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren
            exact Option.some.inj fires ▸ IotaHeadStep.iotaOptionMatchNone

theorem optionMatchSomeRowFiringToIotaHead {scope : Nat}
    (elimPayload : optionMatchSomeIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren optionMatchSomeIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : optionMatchSomeIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen optionMatchSomeIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons noneBranch restTwo =>
      cases restTwo with
      | childCons someBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons value someNil =>
              cases someNil
              exact Option.some.inj fires ▸ IotaHeadStep.iotaOptionMatchSome

theorem eitherMatchInlRowFiringToIotaHead {scope : Nat}
    (elimPayload : eitherMatchInlIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren eitherMatchInlIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : eitherMatchInlIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen eitherMatchInlIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons leftBranch restTwo =>
      cases restTwo with
      | childCons rightBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons value inlNil =>
              cases inlNil
              exact Option.some.inj fires ▸ IotaHeadStep.iotaEitherMatchInl

theorem eitherMatchInrRowFiringToIotaHead {scope : Nat}
    (elimPayload : eitherMatchInrIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren eitherMatchInrIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : eitherMatchInrIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen eitherMatchInrIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons leftBranch restTwo =>
      cases restTwo with
      | childCons rightBranch restThree =>
        cases restThree with
        | childCons scrutineeChild restNil =>
          cases restNil
          cases scrutineeChild with
          | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            intro fires
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons value inrNil =>
              cases inrNil
              exact Option.some.inj fires ▸ IotaHeadStep.iotaEitherMatchInr

theorem idJReflRowFiringToIotaHead {scope : Nat}
    (elimPayload : idJReflIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren idJReflIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : idJReflIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen idJReflIotaRow.elimGenerator elimPayload spine) reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons baseCase restTwo =>
      cases restTwo with
      | childCons scrutineeChild restNil =>
        cases restNil
        cases scrutineeChild with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
          intro fires
          have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
          subst isHead
          cases scrutineeChildren with
          | childCons rawWitness reflNil =>
            cases reflNil
            exact Option.some.inj fires ▸ IotaHeadStep.iotaIdJRefl

theorem idStrictRecReflRowFiringToIotaHead {scope : Nat}
    (elimPayload : idStrictRecReflIotaRow.elimGenerator.payload scope)
    {spine :
      RawTermChildren idStrictRecReflIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires :
      idStrictRecReflIotaRow.firesOn? elimPayload spine = some reduct) :
    IotaHeadStep (.mkGen idStrictRecReflIotaRow.elimGenerator elimPayload spine)
      reduct := by
  revert fires
  cases spine with
  | childCons motive restOne =>
    cases restOne with
    | childCons baseCase restTwo =>
      cases restTwo with
      | childCons scrutineeChild restNil =>
        cases restNil
        cases scrutineeChild with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
          intro fires
          have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
          subst isHead
          cases scrutineeChildren with
          | childCons rawWitness reflNil =>
            cases reflNil
            exact Option.some.inj fires ▸ IotaHeadStep.iotaIdStrictRecRefl

/-- The root dispatcher: a firing of ANY legacy row is the bespoke
`Step` — 17-way membership dispatch into the per-row inversions. -/
theorem legacyRootFiringToStep {scope : Nat} {rule : IotaRuleDesc}
    (isRow : rule ∈ legacyIotaRuleTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    Step (.mkGen rule.elimGenerator elimPayload spine) reduct := by
  cases isRow with
  | head => exact betaRowFiringToStep elimPayload fires
  | tail _ isRow => cases isRow with
    | head => exact (boolTrueRowFiringToIotaHead elimPayload fires).toStep
    | tail _ isRow => cases isRow with
      | head => exact (boolFalseRowFiringToIotaHead elimPayload fires).toStep
      | tail _ isRow => cases isRow with
        | head => exact (fstPairRowFiringToIotaHead elimPayload fires).toStep
        | tail _ isRow => cases isRow with
          | head => exact (sndPairRowFiringToIotaHead elimPayload fires).toStep
          | tail _ isRow => cases isRow with
            | head => exact (natElimZeroRowFiringToIotaHead elimPayload fires).toStep
            | tail _ isRow => cases isRow with
              | head => exact (natRecZeroRowFiringToIotaHead elimPayload fires).toStep
              | tail _ isRow => cases isRow with
                | head => exact (natElimSuccRowFiringToIotaHead elimPayload fires).toStep
                | tail _ isRow => cases isRow with
                  | head => exact (natRecSuccRowFiringToIotaHead elimPayload fires).toStep
                  | tail _ isRow => cases isRow with
                    | head =>
                        exact (listElimNilRowFiringToIotaHead elimPayload fires).toStep
                    | tail _ isRow => cases isRow with
                      | head =>
                          exact (listElimConsRowFiringToIotaHead elimPayload fires).toStep
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact (optionMatchNoneRowFiringToIotaHead
                              elimPayload fires).toStep
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact (optionMatchSomeRowFiringToIotaHead
                                elimPayload fires).toStep
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact (eitherMatchInlRowFiringToIotaHead
                                  elimPayload fires).toStep
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact (eitherMatchInrRowFiringToIotaHead
                                    elimPayload fires).toStep
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact (idJReflRowFiringToIotaHead
                                      elimPayload fires).toStep
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact (idStrictRecReflRowFiringToIotaHead
                                        elimPayload fires).toStep
                                  | tail _ isRow => cases isRow

/-- The root dispatcher at the WEAK-HEAD level: a firing of ANY legacy
row is a `WeakHeadStep` — the beta row through `HeadStep.toWeakHeadStep`,
every iota row through `IotaHeadStep.toWeakHeadStep` (the `rootIota`
embedding).  The bridge every weak-head-normality refutation consumer
needs to case a TABLE step instead of the bespoke constructors. -/
theorem legacyRootFiringToWeakHeadStep {scope : Nat} {rule : IotaRuleDesc}
    (isRow : rule ∈ legacyIotaRuleTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    WeakHeadStep (.mkGen rule.elimGenerator elimPayload spine) reduct := by
  cases isRow with
  | head => exact (betaRowFiringToHeadStep elimPayload fires).toWeakHeadStep
  | tail _ isRow => cases isRow with
    | head => exact (boolTrueRowFiringToIotaHead elimPayload fires).toWeakHeadStep
    | tail _ isRow => cases isRow with
      | head => exact (boolFalseRowFiringToIotaHead elimPayload fires).toWeakHeadStep
      | tail _ isRow => cases isRow with
        | head => exact (fstPairRowFiringToIotaHead elimPayload fires).toWeakHeadStep
        | tail _ isRow => cases isRow with
          | head => exact (sndPairRowFiringToIotaHead elimPayload fires).toWeakHeadStep
          | tail _ isRow => cases isRow with
            | head => exact (natElimZeroRowFiringToIotaHead elimPayload fires).toWeakHeadStep
            | tail _ isRow => cases isRow with
              | head => exact (natRecZeroRowFiringToIotaHead elimPayload fires).toWeakHeadStep
              | tail _ isRow => cases isRow with
                | head => exact (natElimSuccRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                | tail _ isRow => cases isRow with
                  | head => exact (natRecSuccRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                  | tail _ isRow => cases isRow with
                    | head =>
                        exact (listElimNilRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                    | tail _ isRow => cases isRow with
                      | head =>
                          exact (listElimConsRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact (optionMatchNoneRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact (optionMatchSomeRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact (eitherMatchInlRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact (eitherMatchInrRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact (idJReflRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact (idStrictRecReflRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                                  | tail _ isRow => cases isRow

mutual

/-- `StepOverTable legacyIotaRuleTable ⊆ Step` — the backward half of
the IOTA-T1 adequacy. -/
theorem StepOverTable.legacyToStep {scope : Nat}
    {source target : RawTerm scope}
    (tableStep : StepOverTable legacyIotaRuleTable source target) :
    Step source target :=
  match tableStep with
  | .tableRedex isRow elimPayload fires =>
      legacyRootFiringToStep isRow elimPayload fires
  | .cong gen payload childStep =>
      Step.cong gen payload
        (StepOverTableChildren.legacyToStepChildren childStep)

/-- Spine companion of `StepOverTable.legacyToStep`. -/
theorem StepOverTableChildren.legacyToStepChildren {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep :
      StepOverTableChildren legacyIotaRuleTable children children') :
    StepChildren children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepOverTable.legacyToStep headStep)
  | .there head restStep =>
      .there head (StepOverTableChildren.legacyToStepChildren restStep)

end

/-! ## The headline adequacy + the canonical embedding -/

/-- ★ IOTA-T1 ADEQUACY (both directions): the legacy-table relation IS
the bespoke `Step`.  The reduction side of the kernel is faithfully
represented as DATA. -/
theorem stepOverLegacyTable_iff_step {scope : Nat}
    {source target : RawTerm scope} :
    StepOverTable legacyIotaRuleTable source target ↔ Step source target :=
  ⟨StepOverTable.legacyToStep, Step.toLegacyTableStep⟩

/-- Every bespoke `Step` is a full-table `StepTable` step (forward
through the legacy table, then table monotonicity). -/
theorem Step.toStepTable {scope : Nat} {source target : RawTerm scope}
    (sourceSteps : Step source target) : StepTable source target :=
  StepOverTable.monotone (fun isLegacy => legacyRow_memFullTable isLegacy)
    sourceSteps.toLegacyTableStep

/-- Bridge: a LEGACY-table root firing yields a kernel `Step` (via the
table↔Step adequacy), so the table firing migrates the bespoke
`fireRootRedex` onto the table with its kernel-relation soundness
intact.  (The full canonical table's `pathBeta` is intentionally
excluded — it is table-native with no `Step` constructor.) -/
theorem StepTable.fireRootLegacy_imp_step {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq :
      StepTable.fireRootLegacy generator payload children = some reduct) :
    Step (.mkGen generator payload children) reduct :=
  stepOverLegacyTable_iff_step.1
    (fireTableRedexOver_sound legacyIotaRuleTable (fun _ isRow => isRow)
      fireEq)

end FX1Poly.Core
