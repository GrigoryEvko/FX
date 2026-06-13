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

  * FORWARD (`Step.toTableStep`): each bespoke `Step` root
    constructor maps to its row firing BY `rfl` — the IOTA-T0 adequacy
    equations compute the firing on every redex shape.
  * BACKWARD (`StepOverTable.toStep`): a root firing of a legacy
    row yields the bespoke constructor.  The generic inversion trio
    extracts the constructor head POSITIVELY from the firing
    hypothesis, so the 17 per-row inversions are head-substitution +
    spine casing + `Option.some.inj` — no per-row case analysis on
    generators.
  * `stepOverTable_iff_step` — the headline: the legacy-table
    relation IS `Step`.
  * `Step.toStepTable` — the canonical embedding into the full table
    via monotonicity.

Post-swap (`Step` IS the table-driven relation) the adequacy is a
structural identity; this file's load-bearing content is the per-row
FIRING INVERSION layer (each row's successful firing pins the redex
shape and reconstructs the head-step witness) plus the root dispatchers
(`legacyRootFiringToWeakHeadStep`, `Step.weakHeadOrChildCong`,
`Step.childCongruenceOfElimHeadsExcluded`) every destruction site
dispatches through.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditStepTable.lean`. -/

namespace FX1Poly.Core

/-! ## FORWARD adequacy: every Step is a canonical-table step

Both directions are two-arm structural identities over the
`StepChildren`/`StepOverTableChildren` mutuals. -/

mutual

/-- `Step ⊆ StepOverTable iotaRuleTable` — the forward half of the
adequacy, a structural identity. -/
theorem Step.toTableStep {scope : Nat} {source target : RawTerm scope} :
    Step source target → StepOverTable iotaRuleTable source target
  | .tableRedex isRow elimPayload fires => .tableRedex isRow elimPayload fires
  | .cong gen payload childStep =>
      .cong gen payload (StepChildren.toTableStepChildren childStep)

/-- Spine companion of `Step.toTableStep`. -/
theorem StepChildren.toTableStepChildren {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope} :
    StepChildren children children' →
    StepOverTableChildren iotaRuleTable children children'
  | .here rest childStep => .here rest (Step.toTableStep childStep)
  | .there head restStep =>
      .there head (StepChildren.toTableStepChildren restStep)

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

/-- `StepOverTable iotaRuleTable ⊆ Step` — the backward half of the
adequacy, a structural identity. -/
theorem StepOverTable.toStep {scope : Nat}
    {source target : RawTerm scope}
    (tableStep : StepOverTable iotaRuleTable source target) :
    Step source target :=
  match tableStep with
  | .tableRedex isRow elimPayload fires =>
      .tableRedex isRow elimPayload fires
  | .cong gen payload childStep =>
      Step.cong gen payload
        (StepOverTableChildren.toStepChildren childStep)

/-- Spine companion of `StepOverTable.toStep`. -/
theorem StepOverTableChildren.toStepChildren {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep :
      StepOverTableChildren iotaRuleTable children children') :
    StepChildren children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepOverTable.toStep headStep)
  | .there head restStep =>
      .there head (StepOverTableChildren.toStepChildren restStep)

end

/-! ## The headline adequacy + the canonical embedding -/

/-- ★ THE ADEQUACY (both directions): the canonical-table relation IS
`Step` — a structural identity.  The reduction side of the kernel is
faithfully represented as DATA. -/
theorem stepOverTable_iff_step {scope : Nat}
    {source target : RawTerm scope} :
    StepOverTable iotaRuleTable source target ↔ Step source target :=
  ⟨StepOverTable.toStep, Step.toTableStep⟩


/-- **Every canonical-table root firing is a weak-head step.**  21-arm
row dispatch: the 17 bespoke-heritage rows compose their per-row
head-step inversions; the four table-native rows (endpoint-beta,
quot/trunc) land their own `WeakHeadStep` constructors — since
`WeakHeadStep` now absorbs all 21 rows the dispatcher is UNCONDITIONAL
(no foreign-head hypothesis). -/
theorem canonicalRootFiringToWeakHeadStep {scope : Nat}
    {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    WeakHeadStep (.mkGen rule.elimGenerator elimPayload spine) reduct := by
  cases isRow with
  | head =>
      exact (betaRowFiringToHeadStep elimPayload fires).toWeakHeadStep
  | tail _ isRow => cases isRow with
    | head =>
        exact (boolTrueRowFiringToIotaHead elimPayload fires).toWeakHeadStep
    | tail _ isRow => cases isRow with
      | head =>
          exact (boolFalseRowFiringToIotaHead elimPayload fires).toWeakHeadStep
      | tail _ isRow => cases isRow with
        | head =>
            exact (fstPairRowFiringToIotaHead elimPayload fires).toWeakHeadStep
        | tail _ isRow => cases isRow with
          | head =>
              exact (sndPairRowFiringToIotaHead elimPayload fires).toWeakHeadStep
          | tail _ isRow => cases isRow with
            | head =>
                exact (natElimZeroRowFiringToIotaHead elimPayload fires).toWeakHeadStep
            | tail _ isRow => cases isRow with
              | head =>
                  exact (natRecZeroRowFiringToIotaHead elimPayload fires).toWeakHeadStep
              | tail _ isRow => cases isRow with
                | head =>
                    exact (natElimSuccRowFiringToIotaHead elimPayload fires).toWeakHeadStep
                | tail _ isRow => cases isRow with
                  | head =>
                      exact (natRecSuccRowFiringToIotaHead elimPayload fires).toWeakHeadStep
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
                                  | tail _ isRow => cases isRow with
                                    | head => exact WeakHeadStep.pathBeta fires
                                    | tail _ isRow => cases isRow with
                                      | head => exact WeakHeadStep.quotRecMk fires
                                      | tail _ isRow => cases isRow with
                                        | head => exact WeakHeadStep.quotElimMk fires
                                        | tail _ isRow => cases isRow with
                                          | head => exact WeakHeadStep.truncRecIntro fires
                                          | tail _ isRow => cases isRow

/-- **Child congruence for heads OUTSIDE the operational table** — the
generic former-rigidity engine: if a lookup table (formation / flat /
term-indexed / any future classifier) is `none` on every legacy row's
eliminator head, then a `Step` out of a cell whose head the lookup
CLASSIFIES (`some rule`) cannot be a root firing — it is a child
congruence.  ONE freed-subject table inversion replaces the 17
per-constructor `nomatch` arms in every consumer; a new iota row owes
one `rfl` entry in each consumer's exclusion certificate, a new
CLASSIFIED former is absorbed zero-touch. -/
theorem Step.childCongruenceOfElimHeadsExcluded {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {target : RawTerm scope}
    {tableValue : Type} {tableLookup : Generator → Option tableValue}
    {rule : tableValue}
    (excludesElimHeads : ∀ row : IotaRuleDesc,
      row ∈ iotaRuleTable → tableLookup row.elimGenerator = none)
    (isClassified : tableLookup generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children'
      ∧ StepChildren children children' := by
  rcases StepOverTable.invertOrCong
      (stepOverTable_iff_step.mpr step) rfl with
    ⟨rowRule, isRow, elimPayload, spine, cellEq, _fires⟩
    | ⟨children', targetEq, childrenStep⟩
  · have headEq : rowRule.elimGenerator = generator :=
      congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        cellEq
    have isExcluded : tableLookup generator = none :=
      headEq ▸ excludesElimHeads rowRule isRow
    rw [isExcluded] at isClassified
    nomatch isClassified
  · exact ⟨children', targetEq,
      StepOverTableChildren.toStepChildren childrenStep⟩

/-- **The master root dispatcher: weak-head step or child congruence.**
Every `Step` out of a cell either IS a weak-head step to the SAME
target (a root firing, composed through the per-row head-step
inversions) or is a child congruence preserving generator and payload.
This is the strong form of the root/cong dichotomy: because
`WeakHeadStep`'s constructors carry LITERAL eliminator heads, casing
the first disjunct at a concrete subject head auto-discharges every
mismatched arm by index unification — restoring, for the table-driven
relation, exactly the dispatch economy the bespoke per-constructor
`Step` arms used to provide.  ONE freed-subject inversion serves every
eliminator-specific inversion lemma downstream. -/
theorem Step.weakHeadOrChildCong {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {target : RawTerm scope}
    (step : Step (.mkGen generator payload children) target) :
    WeakHeadStep (.mkGen generator payload children) target ∨
    ∃ childrenAfter, target = .mkGen generator payload childrenAfter
      ∧ StepChildren children childrenAfter := by
  rcases StepOverTable.invertOrCong
      (stepOverTable_iff_step.mpr step) rfl with
    ⟨rowRule, isRow, elimPayload, spine, cellEq, fires⟩
    | ⟨childrenAfter, targetEq, childrenStep⟩
  · exact Or.inl
      (cellEq ▸ canonicalRootFiringToWeakHeadStep isRow elimPayload fires)
  · exact Or.inr ⟨childrenAfter, targetEq,
      StepOverTableChildren.toStepChildren childrenStep⟩

/-- Every `Step` is a full-table `StepTable` step — the forward
adequacy verbatim (`StepTable` is the canonical-table instance). -/
theorem Step.toStepTable {scope : Nat} {source target : RawTerm scope}
    (sourceSteps : Step source target) : StepTable source target :=
  sourceSteps.toTableStep

/-- Bridge: a LEGACY-fragment root firing yields a kernel `Step`
(legacy-table soundness, widened by monotonicity into the canonical
table the kernel relation runs on). -/
theorem StepTable.fireRootLegacy_imp_step {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq :
      StepTable.fireRootLegacy generator payload children = some reduct) :
    Step (.mkGen generator payload children) reduct :=
  StepOverTable.toStep
    (StepOverTable.monotone (fun isLegacy => legacyRow_memFullTable isLegacy)
      (fireTableRedexOver_sound legacyIotaRuleTable (fun _ isRow => isRow)
        fireEq))

/-- Bridge at the CANONICAL table: a `StepTable.fireRoot` firing yields
a kernel `Step` — every row of the canonical table, native rows
included, fires into the kernel relation. -/
theorem StepTable.fireRoot_imp_step {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {reduct : RawTerm scope}
    (fireEq :
      StepTable.fireRoot generator payload children = some reduct) :
    Step (.mkGen generator payload children) reduct :=
  StepOverTable.toStep
    (fireTableRedexOver_sound iotaRuleTable (fun _ isRow => isRow) fireEq)

end FX1Poly.Core
