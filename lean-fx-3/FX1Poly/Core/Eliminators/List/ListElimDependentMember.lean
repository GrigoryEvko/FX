import FX1Poly.Core.Eliminators.Core.DependentDataEliminatorMemberSkeleton
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Eliminators.List.ListElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationListElim
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate
import FX1Poly.Core.Metatheory.Canonicity.ListStructuredCandidate

/-! # FX1Poly/Core/ListElimDependentMember
    — dependent `listElim` over a `dataTaitCandidate IsListStructured` scrutinee lands in the motive's candidate

The BINARY recursive-eliminator counterpart of `natElimDependentReducibleMember`.  As there, the cell `listElim
motive scrutinee nilBranch consBranch` must land in an ARBITRARY result candidate (the motive instantiated at the
scrutinee), whose membership is backward-closed only along a WEAK-HEAD step (its `headExpand` interface).  Two
differences from nat, both forced by the BINARY `listCons` constructor:

  * the `cons`-ι does NOT substitute — it fires to a NESTED `gen_app` spine `app (app (app consBranch head) tail)
    (listElim motive nilBranch consBranch tail)`, so nat's `succBranchSubstClosed` premise becomes a
    `consBranchApplicationClosed`: the cons branch applied to a strongly-normalizing head, a structured-candidate
    tail, and the reducible recursive eliminator cell at the tail lands in the result candidate;
  * the outer structural recursion descends the TAIL (the `cons` constructor's recursive argument); the head is
    carried structurally (it appears in the app spine, not as a recursion site).

Per outer structural case, the skeleton peels the (current) scrutinee's weak-head steps; its value-handler fires
the ι:

  * a `listNil`-headed focus fires `iotaListElimNil` to the UNCONDITIONAL `nilBranch` (a member) —
    case-independent;
  * a `listCons`-headed focus, in the `cons` outer case, fires `iotaListElimCons` and discharges the app-spine
    reduct from `consBranchApplicationClosed` applied to the head's strong normalization
    (`listConsCell_head_isStronglyNormalizing`), the tail's candidate membership (`listConsStructuredMember_tail`),
    and the OUTER inductive hypothesis at the tail (realigned onto the structured value's tail by confluence + the
    `listCons` binary-congruence inversion);
  * a `listCons`-headed focus, in the `nil` / `neutralNormal` outer cases, is VACUOUS — the focus reaches the
    structured value (`stepStar_focus_reaches_normal_target`), but a `listCons` cell never reduces to `listNil` or
    to a neutral (`stepStar_under_binaryCell` + the head discriminators).

## Zero-axiom verification

Structural `induction` on the three `IsListStructured` constructors driving three
`dependentDataEliminatorMemberFromValueDispatch` instantiations (shared non-value-handler premises hoisted into
`runDispatch`); the trichotomy is `dataTaitFocusTrichotomyOfValueHeadOrNeutral` over the list constructor heads
with shape recovery (`eq_listNilCell_of_rootGenerator` / `exists_head_tail_of_rootGenerator_listCons`); the
value-handler fires `IotaHeadStep.iotaListElim{Nil,Cons}.toWeakHeadStep` through `headExpand`; the vacuity legs use
`stepStar_under_binaryCell listConsCell Step.from_listCons` and `Generator.noConfusion` /
`isNeutral_rootGenerator_ne_listCons`.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core
open StepStar

/-- The `listElim` cons-ι contractum — `app (app (app consBranch head) tail) (listElim motive nilBranch consBranch
tail)` (mirrors Core's own private `listElimConsContractum` byte-for-byte; the recursive `listElim` subterm is
`listElimCellSpine motive tail nilBranch consBranch`). -/
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

/-- **Dependent `listElim` reducibility over a structural-candidate scrutinee.**  The binary recursive-eliminator
strengthening of `boolElimDependentReducibleMember` / `natElimDependentReducibleMember`: the cell lands in an
arbitrary `resultCandidate` (the motive at the scrutinee), with the `cons`-ι's app-spine reduct discharged from
`consBranchApplicationClosed` applied to the head's strong normalization, the tail's candidate membership, and the
recursive eliminator cell at the tail.  Wraps the shared dependent-elim dispatch in a structural recursion on the
structured value the scrutinee reaches; the recursion descends the TAIL. -/
theorem listElimDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (nilBranchMember : resultCandidate nilBranch)
    (consBranchStronglyNormalizing : IsStronglyNormalizing consBranch)
    (consContractumTerminates :
      ∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractum motive consBranch head tail nilBranch))
    (consBranchApplicationClosed : ∀ {head tail : RawTerm scope},
        IsStronglyNormalizing head →
        dataTaitCandidate IsListStructured tail →
        resultCandidate (listElimCellSpine motive tail nilBranch consBranch) →
        resultCandidate (listElimConsContractum motive consBranch head tail nilBranch))
    (scrutineeMember : dataTaitCandidate IsListStructured scrutinee) :
    resultCandidate (listElimCellSpine motive scrutinee nilBranch consBranch) := by
  -- Forward closure of the structural candidate along a whole reduction (CR2 iterated), implication in the
  -- conclusion so the induction hypothesis carries the membership through each step.
  have memberClosedUnderStepStar : ∀ {source target : RawTerm scope},
      StepStar source target → dataTaitCandidate IsListStructured source →
      dataTaitCandidate IsListStructured target := by
    intro source target chain
    induction chain with
    | refl _ => exact fun member => member
    | trans firstStep _restChain restInductiveHypothesis =>
        exact fun member => restInductiveHypothesis (member.closedUnderStep firstStep)
  -- The shared dispatch with every non-value-handler premise baked in; only the value-handler and the scrutinee
  -- member vary across the structural cases.
  have runDispatch : ∀ {currentScrutinee : RawTerm scope},
      dataTaitCandidate IsListStructured currentScrutinee →
      (∀ {focus : RawTerm scope},
        (focus = listNilCell ∨ ∃ head tail : RawTerm scope, focus = listConsCell head tail) →
        StepStar currentScrutinee focus →
        IsStronglyNormalizing (listElimCellSpine motive focus nilBranch consBranch) →
        resultCandidate (listElimCellSpine motive focus nilBranch consBranch)) →
      resultCandidate (listElimCellSpine motive currentScrutinee nilBranch consBranch) :=
    fun currentMember valueHandler =>
      dependentDataEliminatorMemberFromValueDispatch
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
            focusStronglyNormalizing motiveStronglyNormalizing (candidateMembersSN nilBranchMember)
            consBranchStronglyNormalizing)
        (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeListElim focusWeakHead)
        (spineNeutral := fun focusNeutral => IsNeutral.listElim focusNeutral)
        (headExpand := headExpand)
        (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
        (valueHandler := valueHandler)
        (scrutineeMember := currentMember)
  -- The structured value the scrutinee reaches; recurse on its `IsListStructured` derivation (descending the tail).
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    listStructuredMemberReachesStructuredValue scrutineeMember
  suffices aux : ∀ {structured : RawTerm scope}, IsListStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsListStructured currentScrutinee →
        StepStar currentScrutinee structured →
        resultCandidate (listElimCellSpine motive currentScrutinee nilBranch consBranch) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
  clear scrutineeReachesValue scrutineeMember scrutinee structuredValue structuredValueIsStructured
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | nil =>
      intro currentScrutinee currentMember scrutineeReachesNil
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesNil : StepStar (listConsCell head tail) listNilCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNil rfl
        obtain ⟨_headAfter, _tailAfter, nilEqualsCons, _, _⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesNil head tail rfl
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator nilEqualsCons)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      intro currentScrutinee currentMember scrutineeReachesNeutral
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesNeutral : StepStar (listConsCell head tail) neutralTerm :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNeutral
            neutralTermIsNormal
        obtain ⟨_headAfter, _tailAfter, neutralEqualsCons, _, _⟩ :=
          stepStar_under_binaryCell listConsCell Step.from_listCons focusReachesNeutral head tail rfl
        exact (isNeutral_rootGenerator_ne_listCons (neutralEqualsCons ▸ neutralTermIsNeutral) rfl).elim
  | @cons valueHead valueTail valueHeadNormal valueTailIsStructured outerInductiveHypothesis =>
      intro currentScrutinee currentMember scrutineeReachesCons
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨head, tail, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember cellStronglyNormalizing
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
        subst tailAfterEqualsValue
        have focusMember : dataTaitCandidate IsListStructured (listConsCell head tail) :=
          memberClosedUnderStepStar scrutineeReachesFocus currentMember
        have headStronglyNormalizing : IsStronglyNormalizing head :=
          listConsCell_head_isStronglyNormalizing focusMember.1
        have tailMember : dataTaitCandidate IsListStructured tail :=
          listConsStructuredMember_tail focusMember
        have tailCellMember :
            resultCandidate (listElimCellSpine motive tail nilBranch consBranch) :=
          outerInductiveHypothesis tailMember tailReachesAfter
        exact headExpand IotaHeadStep.iotaListElimCons.toWeakHeadStep
          (consBranchApplicationClosed headStronglyNormalizing tailMember tailCellMember) cellStronglyNormalizing

end FX1Poly.Core
