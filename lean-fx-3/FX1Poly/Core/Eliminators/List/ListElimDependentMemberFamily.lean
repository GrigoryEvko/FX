import FX1Poly.Core.Eliminators.List.ListElimDependentMember
import FX1Poly.Core.Eliminators.List.ListElimReductTrackingStrongNormalization
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ReachAwareListModelCandidate

/-! # FX1Poly/Core/ListElimDependentMemberFamily
    — dependent `listElim` over a VALUE-INDEXED candidate family (the genuinely dependent list recursor)

`listElimDependentReducibleMember` (the fixed-candidate keystone) proves the cell lands in a SINGLE
`resultCandidate`.  That is exactly right when the motive is non-dependent (every `subst0 motive v` shares one
candidate), but the genuinely DEPENDENT recursor needs more: the recursive cell at a tail has type
`subst0 motive tail`, NOT convertible to `subst0 motive scrutinee` (since `scrutinee ↠ listCons head tail`), so
the tail cell lives in a DIFFERENT candidate than the goal — exactly as for nat's predecessor.  The list twin of
`natElimDependentReducibleMemberFamily`.

The fix is a candidate FAMILY `resultCandidateAt : value → (RawTerm → Prop)` — the candidate of `subst0 motive
value` — reduction-stable (`StepStar v w → resultCandidateAt v ≈ resultCandidateAt w`).  The structural recursion
already tracks the structured value at each level; this file threads the family through it, so the tail cell lands
in `resultCandidateAt tail` and the cons result in `resultCandidateAt (listCons head tail)` — both type-correct.
The fixed keystone is the constant-family instance.

Unlike the keystone, where firing `iotaListElimNil` to `nilBranch` is sound in EVERY case (the single candidate
absorbs it), the family's `nilBranchMember` lives only at `listNilCell`'s candidate, so a `listNil`-headed focus is
fired ONLY in the `nil` case; in the `neutralNormal` / `cons` cases it is VACUOUS (a `listNil` value cannot reach a
normal neutral or a `listCons` value — confluence + the head discriminators).  Symmetrically the `listCons`-headed
focus fires `iotaListElimCons` only in the `cons` case and is vacuous in `nil` / `neutralNormal`.

The bounded FT bridge instantiates `resultCandidateAt v := IsReducibleMemberAtBounded env bound (subst0 motive v)`
and discharges `candidateStable` from `subst0`-congruence + the bounded model's Conv-invariance.

## Zero-axiom verification

The same structural `induction` on `IsListStructured` driving the shared `dependentDataEliminatorMemberFromValue\
Dispatch` per case (at the case's value-indexed candidate), with the family's stability iff threaded at three
points (top reduction, the tail descent, the `listCons` congruence) and the off-constructor focus vacuities
discharged by confluence + `StepStar.eq_of_noStep` + `IsNeutral.rootGenerator_ne_listNil` /
`isNeutral_rootGenerator_ne_listCons` / `Generator.noConfusion`.  No `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core
open StepStar

/-- The `listElim` cons-ι contractum — mirrors Core's own private `listElimConsContractum` byte-for-byte. -/
private abbrev listElimConsContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons tail .childNil)))))
        .childNil))

/-- **Dependent `listElim` reducibility over a value-indexed candidate family — SELF-CONTAINED cell SN (no false
firing premise).**  The false-premise-free strengthening of `listElimDependentReducibleMemberFamily` (the
`listElim` twin of `natElimDependentReducibleMemberFamilySelfContained`): it drops the bare-SN firing obligation
`consContractumTerminates` (false over arbitrary branches — applying an SN function to an SN argument is not SN,
the Omega counterexample) and instead derives cell SN at each scrutinee focus from the SCRUTINEE-REDUCING
four-fold engine `listElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN`, fed
through the member-keyed dispatch `dependentDataEliminatorMemberFromValueDispatchMemberKeyed`.

The engine's `originalContractumSN` obligation (the cons-iota app-chain contractum is SN whenever the focus
reaches a cons cell) is supplied per structured-value-recursion level by `contractumSNAtCurrent`: at the `cons`
level it is the GENUINE recursive derivation — the firing tail reaches `valueTail`, the structural IH gives its
recursive cell member (transported across `tail ↠ valueTail` by `candidateStable`), so the cons-branch
application closure `consBranchApplicationClosed` lands the app-chain contractum in the result candidate, whose
CR1 (`candidateMembersSN`) is exactly the contractum SN the engine needs; at the `nil` / `neutralNormal` levels it
is VACUOUS (a structured value reaching both a normal non-cons and a cons cell is refuted by confluence +
`Generator.noConfusion` / the neutral-vs-`listCons` head clash).  Cell SN is now bundled with membership through
the well-founded structured-value recursion, never assumed.

## Zero-axiom verification

Same structural `induction` on `IsListStructured` driving the member-keyed dispatch per case, with the four-fold
reduct-tracking SN engine supplying cell SN from the in-recursion app-chain contractum membership.  No `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration swept by
`#audit_namespace FX1Poly.Core`. -/
theorem listElimDependentReducibleMemberFamilySelfContained {scope : Nat}
    (carrierCandidate : RawTerm scope → Prop)
    (resultCandidateAt : RawTerm scope → RawTerm scope → Prop)
    (candidateMembersSN : ∀ {value term : RawTerm scope}, reachAwareListCandidate carrierCandidate value →
        resultCandidateAt value term → IsStronglyNormalizing term)
    (headExpand : ∀ {value redexTerm contractum : RawTerm scope}, reachAwareListCandidate carrierCandidate value →
        WeakHeadStep redexTerm contractum → resultCandidateAt value contractum →
        IsStronglyNormalizing redexTerm → resultCandidateAt value redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {value neutralTerm : RawTerm scope},
        reachAwareListCandidate carrierCandidate value →
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidateAt value neutralTerm)
    (candidateStable : ∀ {value valueReduct term : RawTerm scope},
        reachAwareListCandidate carrierCandidate value → StepStar value valueReduct →
        (resultCandidateAt value term ↔ resultCandidateAt valueReduct term))
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (nilBranchMember : resultCandidateAt listNilCell nilBranch)
    (consBranchStronglyNormalizing : IsStronglyNormalizing consBranch)
    (consBranchApplicationClosed : ∀ {head tail : RawTerm scope},
        carrierCandidate head →
        reachAwareListCandidate carrierCandidate tail →
        resultCandidateAt tail (listElimCellSpine motive tail nilBranch consBranch) →
        resultCandidateAt (listConsCell head tail) (listElimConsContractum motive consBranch head tail nilBranch))
    (scrutineeMember : reachAwareListCandidate carrierCandidate scrutinee) :
    resultCandidateAt scrutinee (listElimCellSpine motive scrutinee nilBranch consBranch) := by
  have runDispatchAt : ∀ {structuredValue : RawTerm scope}, dataTaitCandidate IsListStructured structuredValue →
      reachAwareListCandidate carrierCandidate structuredValue →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsListStructured currentScrutinee →
      (∀ (head tail : RawTerm scope), StepStar currentScrutinee (listConsCell head tail) →
        IsStronglyNormalizing (listElimConsContractum motive consBranch head tail nilBranch)) →
      (∀ {focus : RawTerm scope},
        (focus = listNilCell ∨ ∃ head tail : RawTerm scope, focus = listConsCell head tail) →
        StepStar currentScrutinee focus →
        IsStronglyNormalizing (listElimCellSpine motive focus nilBranch consBranch) →
        resultCandidateAt structuredValue (listElimCellSpine motive focus nilBranch consBranch)) →
      resultCandidateAt structuredValue (listElimCellSpine motive currentScrutinee nilBranch consBranch) := by
    intro structuredValue structuredWitness structuredReachAware currentScrutinee currentMember
      contractumSNAtCurrent valueHandler
    exact dependentDataEliminatorMemberFromValueDispatchMemberKeyed
        (isValue := fun focus =>
          focus = listNilCell ∨ ∃ head tail : RawTerm scope, focus = listConsCell head tail)
        (scrutineeCandidate := dataTaitCandidate IsListStructured)
        (elimSpine := fun focus => listElimCellSpine motive focus nilBranch consBranch)
        (focusTrichotomy := fun member =>
          dataTaitFocusTrichotomyOfValueHeadOrNeutral
            (valueHead := fun generator =>
              generator = Generator.gen_listNil ∨ generator = Generator.gen_listCons)
            isListStructured_valueHeadOrNeutral
            (fun headDisjunction =>
              headDisjunction.elim
                (fun nilHead => Or.inl (eq_listNilCell_of_rootGenerator nilHead))
                (fun consHead => Or.inr (exists_head_tail_of_rootGenerator_listCons consHead)))
            member)
        (candidateStronglyNormalizing := fun member => member.1)
        (candidateClosedUnderStep := fun member step => member.closedUnderStep step)
        (spineStronglyNormalizing := fun focusMember focusReaches =>
          listElimCellSpine_isStronglyNormalizing_of_scrutineeReducing_fromOriginalContractumSN
            focusMember.1 motiveStronglyNormalizing
            (candidateMembersSN reachAwareListCandidate_memberOfNormalNil nilBranchMember)
            consBranchStronglyNormalizing
            (fun head tail focusReachesCons =>
              contractumSNAtCurrent head tail
                (StepStar.trans_compose focusReaches focusReachesCons)))
        (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeListElim focusWeakHead)
        (spineNeutral := fun focusNeutral => IsNeutral.listElim focusNeutral)
        (headExpand := fun weakHeadStep contractumMember redexStronglyNormalizing =>
          headExpand structuredReachAware weakHeadStep contractumMember redexStronglyNormalizing)
        (memberOfStronglyNormalizingNeutral := fun neutralStronglyNormalizing neutral =>
          memberOfStronglyNormalizingNeutral structuredReachAware neutralStronglyNormalizing neutral)
        (valueHandler := valueHandler)
        (scrutineeMember := currentMember)
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    listStructuredMemberReachesStructuredValue (reachAwareListCandidate_toWeakListCandidate scrutineeMember)
  refine (candidateStable scrutineeMember scrutineeReachesValue).mpr ?_
  suffices aux : ∀ {structured : RawTerm scope}, IsListStructured structured →
      reachAwareListCandidate carrierCandidate structured →
      ∀ {currentScrutinee : RawTerm scope}, reachAwareListCandidate carrierCandidate currentScrutinee →
        StepStar currentScrutinee structured →
        resultCandidateAt structured (listElimCellSpine motive currentScrutinee nilBranch consBranch) from
    aux structuredValueIsStructured
      (reachAwareListCandidate_closedUnderStepStar scrutineeMember scrutineeReachesValue)
      scrutineeMember scrutineeReachesValue
  clear scrutineeReachesValue scrutineeMember scrutinee structuredValue structuredValueIsStructured
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | nil =>
      intro structuredReachAware currentScrutinee currentMember scrutineeReachesNil
      have currentWeak := reachAwareListCandidate_toWeakListCandidate currentMember
      refine runDispatchAt listNilStructuredMember structuredReachAware currentWeak
        (fun head tail scrutineeReachesCons => ?_)
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      · have consReachesNil : StepStar (listConsCell head tail) listNilCell :=
          stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesCons scrutineeReachesNil rfl
        obtain ⟨_headAfter, _tailAfter, nilEqualsCons, _, _⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons consReachesNil head tail rfl
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator nilEqualsCons)
      · rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
        · subst focusEquation
          exact headExpand structuredReachAware IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember
            cellStronglyNormalizing
        · subst focusEquation
          have focusReachesNil : StepStar (listConsCell head tail) listNilCell :=
            stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesFocus scrutineeReachesNil rfl
          obtain ⟨_headAfter, _tailAfter, nilEqualsCons, _, _⟩ :=
            stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesNil head tail rfl
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator nilEqualsCons)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      intro structuredReachAware currentScrutinee currentMember scrutineeReachesNeutral
      have currentWeak := reachAwareListCandidate_toWeakListCandidate currentMember
      have neutralStructuredMember : dataTaitCandidate IsListStructured neutralTerm :=
        dataTaitCandidate.memberOfValue neutralTermIsNormal
          (IsListStructured.neutralNormal neutralTermIsNeutral neutralTermIsNormal)
      refine runDispatchAt neutralStructuredMember structuredReachAware currentWeak
        (fun head tail scrutineeReachesCons => ?_)
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      · have consReachesNeutral : StepStar (listConsCell head tail) neutralTerm :=
          stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesCons scrutineeReachesNeutral
            neutralTermIsNormal
        obtain ⟨_headAfter, _tailAfter, neutralEqualsCons, _, _⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons consReachesNeutral head tail rfl
        exact (isNeutral_rootGenerator_ne_listCons (neutralEqualsCons ▸ neutralTermIsNeutral) rfl).elim
      · rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
        · subst focusEquation
          have neutralReachesNil : StepStar neutralTerm listNilCell :=
            stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesNeutral scrutineeReachesFocus rfl
          have nilEqualsNeutral : listNilCell = neutralTerm :=
            StepStar.eq_of_noStep
              (fun reduct step => RawTerm.isStepNormalForm_blocks_step neutralTermIsNormal reduct step)
              neutralReachesNil
          exact (IsNeutral.rootGenerator_ne_listNil (nilEqualsNeutral ▸ neutralTermIsNeutral) rfl).elim
        · subst focusEquation
          have focusReachesNeutral : StepStar (listConsCell head tail) neutralTerm :=
            stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesFocus scrutineeReachesNeutral
              neutralTermIsNormal
          obtain ⟨_headAfter, _tailAfter, neutralEqualsCons, _, _⟩ :=
            stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesNeutral head tail rfl
          exact (isNeutral_rootGenerator_ne_listCons (neutralEqualsCons ▸ neutralTermIsNeutral) rfl).elim
  | @cons valueHead valueTail valueHeadNormal valueTailIsStructured outerInductiveHypothesis =>
      intro structuredReachAware currentScrutinee currentMember scrutineeReachesCons
      have currentWeak := reachAwareListCandidate_toWeakListCandidate currentMember
      have valueTailReachAware : reachAwareListCandidate carrierCandidate valueTail :=
        structuredReachAware.reachableConsTailMember (StepStar.refl _)
      have consStructuredMember : dataTaitCandidate IsListStructured (listConsCell valueHead valueTail) :=
        dataTaitCandidate.memberOfValue
          (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured))
          (IsListStructured.cons valueHeadNormal valueTailIsStructured)
      refine runDispatchAt consStructuredMember structuredReachAware currentWeak
        (fun head tail scrutineeReachesConsFocus => ?_)
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      · -- contractumSNAtCurrent at the `cons` level: the genuine recursive derivation supplying the engine's
        -- `originalContractumSN`.  The firing tail reaches `valueTail`; the reach-aware IH gives its recursive cell
        -- member, `consBranchApplicationClosed` lands the app-chain contractum, CR1 extracts its SN.
        have focusReachesCons : StepStar (listConsCell head tail) (listConsCell valueHead valueTail) :=
          stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesConsFocus scrutineeReachesCons
            (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured))
        obtain ⟨_headAfter, tailAfter, consEquation, _headReachesAfter, tailReachesAfter⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesCons head tail rfl
        have tailAfterEqualsValue : tailAfter = valueTail := by
          injection consEquation with _equationOne _equationTwo _equationThree childrenEquation
          injection childrenEquation with _scopeEquation _shiftEquation _restShiftsEquation _headEquation restEquation
          injection restEquation with _scopeEquationTwo _shiftEquationTwo _restShiftsEquationTwo tailEquation
          exact tailEquation.symm
        rw [tailAfterEqualsValue] at tailReachesAfter
        have focusReachAware : reachAwareListCandidate carrierCandidate (listConsCell head tail) :=
          reachAwareListCandidate_closedUnderStepStar currentMember scrutineeReachesConsFocus
        have tailReachAware : reachAwareListCandidate carrierCandidate tail :=
          focusReachAware.reachableConsTailMember (StepStar.refl _)
        have tailCellMember :
            resultCandidateAt tail (listElimCellSpine motive tail nilBranch consBranch) :=
          (candidateStable tailReachAware tailReachesAfter).mpr
            (outerInductiveHypothesis valueTailReachAware tailReachAware tailReachesAfter)
        exact candidateMembersSN focusReachAware
          (consBranchApplicationClosed (focusReachAware.reachableConsHeadMember (StepStar.refl _))
            tailReachAware tailCellMember)
      · rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
        · subst focusEquation
          have nilReachesCons : StepStar listNilCell (listConsCell valueHead valueTail) :=
            stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesFocus scrutineeReachesCons
              (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured))
          have consEqualsNil : listConsCell valueHead valueTail = listNilCell :=
            StepStar.eq_of_noStep
              (fun reduct step =>
                RawTerm.isStepNormalForm_blocks_step
                  (show RawTerm.isStepNormalForm (listNilCell (scope := scope)) from rfl) reduct step)
              nilReachesCons
          exact Generator.noConfusion (congrArg RawTerm.rootGenerator consEqualsNil)
        · subst focusEquation
          have focusReachesCons : StepStar (listConsCell head tail) (listConsCell valueHead valueTail) :=
            stepStar_focus_reaches_normal_target currentWeak.1 scrutineeReachesFocus scrutineeReachesCons
              (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured))
          obtain ⟨_headAfter, tailAfter, consEquation, _headReachesAfter, tailReachesAfter⟩ :=
            stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesCons head tail rfl
          have tailAfterEqualsValue : tailAfter = valueTail := by
            injection consEquation with _equationOne _equationTwo _equationThree childrenEquation
            injection childrenEquation with _scopeEquation _shiftEquation _restShiftsEquation _headEquation restEquation
            injection restEquation with _scopeEquationTwo _shiftEquationTwo _restShiftsEquationTwo tailEquation
            exact tailEquation.symm
          rw [tailAfterEqualsValue] at tailReachesAfter
          have focusReachAware : reachAwareListCandidate carrierCandidate (listConsCell head tail) :=
            reachAwareListCandidate_closedUnderStepStar currentMember scrutineeReachesFocus
          have tailReachAware : reachAwareListCandidate carrierCandidate tail :=
            focusReachAware.reachableConsTailMember (StepStar.refl _)
          have tailCellMember :
              resultCandidateAt tail (listElimCellSpine motive tail nilBranch consBranch) :=
            (candidateStable tailReachAware tailReachesAfter).mpr
              (outerInductiveHypothesis valueTailReachAware tailReachAware tailReachesAfter)
          have consReductMember :
              resultCandidateAt (listConsCell valueHead valueTail)
                (listElimConsContractum motive consBranch head tail nilBranch) :=
            (candidateStable focusReachAware focusReachesCons).mp
              (consBranchApplicationClosed (focusReachAware.reachableConsHeadMember (StepStar.refl _))
                tailReachAware tailCellMember)
          exact headExpand structuredReachAware IotaHeadStep.iotaListElimCons.toWeakHeadStep consReductMember
            cellStronglyNormalizing

/-- **Dependent `listElim` reducibility over a value-indexed candidate family.**  The genuinely-dependent
strengthening of `listElimDependentReducibleMember`: each scrutinee-value `v` carries its own result candidate
`resultCandidateAt v` (the motive at `v`), the family being reduction-stable; the recursive tail cell lands in
`resultCandidateAt tail`, the `cons`-ι reduct in `resultCandidateAt (listCons head tail)`. -/
theorem listElimDependentReducibleMemberFamily {scope : Nat}
    (resultCandidateAt : RawTerm scope → RawTerm scope → Prop)
    (candidateMembersSN : ∀ {value term : RawTerm scope}, dataTaitCandidate IsListStructured value →
        resultCandidateAt value term → IsStronglyNormalizing term)
    (headExpand : ∀ {value redexTerm contractum : RawTerm scope}, dataTaitCandidate IsListStructured value →
        WeakHeadStep redexTerm contractum → resultCandidateAt value contractum →
        IsStronglyNormalizing redexTerm → resultCandidateAt value redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {value neutralTerm : RawTerm scope},
        dataTaitCandidate IsListStructured value →
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidateAt value neutralTerm)
    (candidateStable : ∀ {value valueReduct term : RawTerm scope},
        dataTaitCandidate IsListStructured value → StepStar value valueReduct →
        (resultCandidateAt value term ↔ resultCandidateAt valueReduct term))
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (nilBranchMember : resultCandidateAt listNilCell nilBranch)
    (consBranchStronglyNormalizing : IsStronglyNormalizing consBranch)
    (consContractumTerminates :
      ∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractum motive consBranch head tail nilBranch))
    (consBranchApplicationClosed : ∀ {head tail : RawTerm scope},
        IsStronglyNormalizing head →
        dataTaitCandidate IsListStructured tail →
        resultCandidateAt tail (listElimCellSpine motive tail nilBranch consBranch) →
        resultCandidateAt (listConsCell head tail) (listElimConsContractum motive consBranch head tail nilBranch))
    (scrutineeMember : dataTaitCandidate IsListStructured scrutinee) :
    resultCandidateAt scrutinee (listElimCellSpine motive scrutinee nilBranch consBranch) := by
  -- Forward closure of the structural candidate along a whole reduction (CR2 iterated).
  have memberClosedUnderStepStar : ∀ {source target : RawTerm scope},
      StepStar source target → dataTaitCandidate IsListStructured source →
      dataTaitCandidate IsListStructured target := by
    intro source target chain
    induction chain with
    | refl _ => exact fun member => member
    | trans firstStep _restChain restInductiveHypothesis =>
        exact fun member => restInductiveHypothesis (member.closedUnderStep firstStep)
  -- The shared dispatch at the candidate of a FIXED structured value, parameterized by that value's structured
  -- membership (which the per-value `headExpand` / neutral closures need).
  have runDispatchAt : ∀ {structuredValue : RawTerm scope}, dataTaitCandidate IsListStructured structuredValue →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsListStructured currentScrutinee →
      (∀ {focus : RawTerm scope},
        (focus = listNilCell ∨ ∃ head tail : RawTerm scope, focus = listConsCell head tail) →
        StepStar currentScrutinee focus →
        IsStronglyNormalizing (listElimCellSpine motive focus nilBranch consBranch) →
        resultCandidateAt structuredValue (listElimCellSpine motive focus nilBranch consBranch)) →
      resultCandidateAt structuredValue (listElimCellSpine motive currentScrutinee nilBranch consBranch) := by
    intro structuredValue structuredWitness currentScrutinee currentMember valueHandler
    exact dependentDataEliminatorMemberFromValueDispatch
        (isValue := fun focus =>
          focus = listNilCell ∨ ∃ head tail : RawTerm scope, focus = listConsCell head tail)
        (scrutineeCandidate := dataTaitCandidate IsListStructured)
        (elimSpine := fun focus => listElimCellSpine motive focus nilBranch consBranch)
        (focusTrichotomy := fun member =>
          dataTaitFocusTrichotomyOfValueHeadOrNeutral
            (valueHead := fun generator =>
              generator = Generator.gen_listNil ∨ generator = Generator.gen_listCons)
            isListStructured_valueHeadOrNeutral
            (fun headDisjunction =>
              headDisjunction.elim
                (fun nilHead => Or.inl (eq_listNilCell_of_rootGenerator nilHead))
                (fun consHead => Or.inr (exists_head_tail_of_rootGenerator_listCons consHead)))
            member)
        (candidateStronglyNormalizing := fun member => member.1)
        (candidateClosedUnderStep := fun member step => member.closedUnderStep step)
        (spineStronglyNormalizing := fun focusStronglyNormalizing =>
          listElim_isStronglyNormalizing_of_strongly_normalizing_branches consContractumTerminates
            focusStronglyNormalizing motiveStronglyNormalizing
            (candidateMembersSN listNilStructuredMember nilBranchMember) consBranchStronglyNormalizing)
        (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeListElim focusWeakHead)
        (spineNeutral := fun focusNeutral => IsNeutral.listElim focusNeutral)
        (headExpand := fun weakHeadStep contractumMember redexStronglyNormalizing =>
          headExpand structuredWitness weakHeadStep contractumMember redexStronglyNormalizing)
        (memberOfStronglyNormalizingNeutral := fun neutralStronglyNormalizing neutral =>
          memberOfStronglyNormalizingNeutral structuredWitness neutralStronglyNormalizing neutral)
        (valueHandler := valueHandler)
        (scrutineeMember := currentMember)
  -- The structured value the scrutinee reaches; recurse on its `IsListStructured` derivation (descending the tail).
  -- The aux conclusion is at the STRUCTURED value's candidate; the top closes back to the scrutinee's by stability.
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    listStructuredMemberReachesStructuredValue scrutineeMember
  refine (candidateStable scrutineeMember scrutineeReachesValue).mpr ?_
  suffices aux : ∀ {structured : RawTerm scope}, IsListStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsListStructured currentScrutinee →
        StepStar currentScrutinee structured →
        resultCandidateAt structured (listElimCellSpine motive currentScrutinee nilBranch consBranch) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
  clear scrutineeReachesValue scrutineeMember scrutinee structuredValue structuredValueIsStructured
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | nil =>
      intro currentScrutinee currentMember scrutineeReachesNil
      refine runDispatchAt listNilStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
      · subst focusEquation
        exact headExpand listNilStructuredMember IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember
          cellStronglyNormalizing
      · subst focusEquation
        have focusReachesNil : StepStar (listConsCell head tail) listNilCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNil rfl
        obtain ⟨_headAfter, _tailAfter, nilEqualsCons, _, _⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesNil head tail rfl
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator nilEqualsCons)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      intro currentScrutinee currentMember scrutineeReachesNeutral
      have neutralStructuredMember : dataTaitCandidate IsListStructured neutralTerm :=
        dataTaitCandidate.memberOfValue neutralTermIsNormal
          (IsListStructured.neutralNormal neutralTermIsNeutral neutralTermIsNormal)
      refine runDispatchAt neutralStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
      · subst focusEquation
        -- VACUOUS: the scrutinee reaches both `listNil` (focus) and the normal neutral `neutralTerm`.
        have neutralReachesNil : StepStar neutralTerm listNilCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesNeutral scrutineeReachesFocus rfl
        have nilEqualsNeutral : listNilCell = neutralTerm :=
          StepStar.eq_of_noStep
            (fun reduct step => RawTerm.isStepNormalForm_blocks_step neutralTermIsNormal reduct step)
            neutralReachesNil
        exact (IsNeutral.rootGenerator_ne_listNil (nilEqualsNeutral ▸ neutralTermIsNeutral) rfl).elim
      · subst focusEquation
        have focusReachesNeutral : StepStar (listConsCell head tail) neutralTerm :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNeutral
            neutralTermIsNormal
        obtain ⟨_headAfter, _tailAfter, neutralEqualsCons, _, _⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesNeutral head tail rfl
        exact (isNeutral_rootGenerator_ne_listCons (neutralEqualsCons ▸ neutralTermIsNeutral) rfl).elim
  | @cons valueHead valueTail valueHeadNormal valueTailIsStructured outerInductiveHypothesis =>
      intro currentScrutinee currentMember scrutineeReachesCons
      have consStructuredMember : dataTaitCandidate IsListStructured (listConsCell valueHead valueTail) :=
        dataTaitCandidate.memberOfValue
          (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured))
          (IsListStructured.cons valueHeadNormal valueTailIsStructured)
      refine runDispatchAt consStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
      · subst focusEquation
        -- VACUOUS: the scrutinee reaches both `listNil` (focus) and the `listCons` structured value.
        have nilReachesCons : StepStar listNilCell (listConsCell valueHead valueTail) :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesCons
            (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured))
        have consEqualsNil : listConsCell valueHead valueTail = listNilCell :=
          StepStar.eq_of_noStep
            (fun reduct step =>
              RawTerm.isStepNormalForm_blocks_step
                (show RawTerm.isStepNormalForm (listNilCell (scope := scope)) from rfl) reduct step)
            nilReachesCons
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator consEqualsNil)
      · subst focusEquation
        have focusReachesCons : StepStar (listConsCell head tail) (listConsCell valueHead valueTail) :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesCons
            (isListStructured_impliesStepNormalForm (IsListStructured.cons valueHeadNormal valueTailIsStructured))
        obtain ⟨_headAfter, tailAfter, consEquation, _headReachesAfter, tailReachesAfter⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesCons head tail rfl
        have tailAfterEqualsValue : tailAfter = valueTail := by
          injection consEquation with _equationOne _equationTwo _equationThree childrenEquation
          injection childrenEquation with _scopeEquation _shiftEquation _restShiftsEquation _headEquation restEquation
          injection restEquation with _scopeEquationTwo _shiftEquationTwo _restShiftsEquationTwo tailEquation
          exact tailEquation.symm
        rw [tailAfterEqualsValue] at tailReachesAfter
        have focusMember : dataTaitCandidate IsListStructured (listConsCell head tail) :=
          memberClosedUnderStepStar scrutineeReachesFocus currentMember
        have headStronglyNormalizing : IsStronglyNormalizing head :=
          listConsCell_head_isStronglyNormalizing focusMember.1
        have tailMember : dataTaitCandidate IsListStructured tail :=
          listConsStructuredMember_tail focusMember
        have tailCellMember :
            resultCandidateAt tail (listElimCellSpine motive tail nilBranch consBranch) :=
          (candidateStable tailMember tailReachesAfter).mpr
            (outerInductiveHypothesis tailMember tailReachesAfter)
        have consReductMember :
            resultCandidateAt (listConsCell valueHead valueTail)
              (listElimConsContractum motive consBranch head tail nilBranch) :=
          (candidateStable focusMember focusReachesCons).mp
            (consBranchApplicationClosed headStronglyNormalizing tailMember tailCellMember)
        exact headExpand consStructuredMember IotaHeadStep.iotaListElimCons.toWeakHeadStep consReductMember
          cellStronglyNormalizing

end FX1Poly.Core
