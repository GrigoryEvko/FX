import FX1Poly.Core.Eliminators.Core.DependentDataEliminatorMemberSkeleton
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim
import FX1Poly.Core.Metatheory.Canonicity.NatStructuredCandidate

/-! # FX1Poly/Core/NatElimDependentMember
    — dependent `natElim` over a `dataTaitCandidate IsNatStructured` scrutinee lands in the motive's candidate

The recursive-eliminator counterpart of `boolElimDependentReducibleMember`.  As there, the cell `natElim motive
scrutinee zeroBranch succBranch` must land in an ARBITRARY result candidate (the motive instantiated at the
scrutinee), whose membership is backward-closed only along a WEAK-HEAD step (its `headExpand` interface).  Unlike
bool, the `succ`-ι does not select an unconditional branch — it fires to `succBranch[var0 := natElim … predecessor,
var1 := predecessor]`, which needs the eliminator cell AT THE PREDECESSOR to already be a member.  That recursive
obligation is not expressible in the FLAT `dependentDataEliminatorMemberFromValueDispatch` value-handler (the
predecessor is a candidate member, not a scrutinee-SN-smaller reduct), so this member wraps the skeleton in a
STRUCTURAL recursion on `IsNatStructured (the structured value the scrutinee reaches)`: each `natSucc` layer of
that value supplies the inductive hypothesis for its predecessor.

Per outer structural case, the skeleton peels the (current) scrutinee's weak-head steps; its value-handler fires
the ι:

  * a `natZero`-headed focus fires `iotaNatElimZero` to the UNCONDITIONAL `zeroBranch` (a member) — case-independent;
  * a `natSucc`-headed focus, in the `succ` outer case, fires `iotaNatElimSucc` and discharges the substituted
    reduct from `succBranchSubstClosed` applied to the predecessor's candidate membership
    (`natSuccStructuredMember_predecessor`) and the OUTER inductive hypothesis at the predecessor (realigned onto the
    structured value's predecessor by confluence + the `natSucc` congruence inversion);
  * a `natSucc`-headed focus, in the `zero` / `neutralNormal` outer cases, is VACUOUS — the focus reaches the
    structured value (`stepStar_focus_reaches_normal_target`), but a `natSucc` cell never reduces to `natZero` or to a
    neutral (`stepStar_under_unaryCell` + the head discriminators).

`natElimStructuredValueMember` (the VALUE regime, scrutinee already `IsNatStructured`) is subsumed: a structured
value is a member (`dataTaitCandidate.memberOfValue`).  The closed scope-0 special case has the neutral disjunct
vacuous.

## Zero-axiom verification

Structural `induction` on the three `IsNatStructured` constructors driving three
`dependentDataEliminatorMemberFromValueDispatch` instantiations (shared non-value-handler premises hoisted into
`runDispatch`); the trichotomy is `dataTaitFocusTrichotomyOfValueHeadOrNeutral` over the nat constructor heads with
shape recovery (`eq_natZeroCell_of_rootGenerator` / `exists_predecessor_of_rootGenerator_natSucc`); the value-handler
fires `IotaHeadStep.iotaNatElim{Zero,Succ}.toWeakHeadStep` through `headExpand`; the vacuity legs use
`stepStar_under_unaryCell natSuccCell Step.from_natSucc` and `Generator.noConfusion` / `isNeutral_rootGenerator_ne_natSucc`.
No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core
open StepStar

/-- **Dependent `natElim` reducibility over a structural-candidate scrutinee.**  The recursive-eliminator
strengthening of `boolElimDependentReducibleMember`: the cell lands in an arbitrary `resultCandidate` (the motive
at the scrutinee), with the `succ`-ι's substituted reduct discharged from `succBranchSubstClosed` applied to the
recursive eliminator cell at the predecessor.  Wraps the shared dependent-elim dispatch in a structural recursion
on the structured value the scrutinee reaches. -/
theorem natElimDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch)
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
        (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (natElimCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc))
    (succBranchSubstClosed : ∀ {predecessor : RawTerm scope},
        dataTaitCandidate IsNatStructured predecessor →
        resultCandidate (natElimCellSpine motive predecessor zeroBranch succBranch) →
        resultCandidate
          (RawTerm.subst
            (RawTermSubst.cons (natElimCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch))
    (scrutineeMember : dataTaitCandidate IsNatStructured scrutinee) :
    resultCandidate (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  -- Forward closure of the structural candidate along a whole reduction (CR2 iterated), implication in the
  -- conclusion so the induction hypothesis carries the membership through each step.
  have memberClosedUnderStepStar : ∀ {source target : RawTerm scope},
      StepStar source target → dataTaitCandidate IsNatStructured source →
      dataTaitCandidate IsNatStructured target := by
    intro source target chain
    induction chain with
    | refl _ => exact fun member => member
    | trans firstStep _restChain restInductiveHypothesis =>
        exact fun member => restInductiveHypothesis (member.closedUnderStep firstStep)
  -- The shared dispatch with every non-value-handler premise baked in; only the value-handler and the scrutinee
  -- member vary across the structural cases.
  have runDispatch : ∀ {currentScrutinee : RawTerm scope},
      dataTaitCandidate IsNatStructured currentScrutinee →
      (∀ {focus : RawTerm scope},
        (focus = natZeroCell ∨ ∃ predecessor : RawTerm scope, focus = natSuccCell predecessor) →
        StepStar currentScrutinee focus →
        IsStronglyNormalizing (natElimCellSpine motive focus zeroBranch succBranch) →
        resultCandidate (natElimCellSpine motive focus zeroBranch succBranch)) →
      resultCandidate (natElimCellSpine motive currentScrutinee zeroBranch succBranch) :=
    fun currentMember valueHandler =>
      dependentDataEliminatorMemberFromValueDispatch
        (isValue := fun focus => focus = natZeroCell ∨ ∃ predecessor : RawTerm scope, focus = natSuccCell predecessor)
        (scrutineeCandidate := dataTaitCandidate IsNatStructured)
        (elimSpine := fun focus => natElimCellSpine motive focus zeroBranch succBranch)
        (focusTrichotomy := fun member =>
          dataTaitFocusTrichotomyOfValueHeadOrNeutral
            (valueHead := fun generator =>
              generator = Generator.gen_natZero ∨ generator = Generator.gen_natSucc)
            isNatStructured_valueHeadOrNeutral
            (fun headDisjunction =>
              headDisjunction.elim
                (fun zeroHead => Or.inl (eq_natZeroCell_of_rootGenerator zeroHead))
                (fun succHead => Or.inr (exists_predecessor_of_rootGenerator_natSucc succHead)))
            member)
        (candidateStronglyNormalizing := fun member => member.1)
        (candidateClosedUnderStep := fun member step => member.closedUnderStep step)
        (spineStronglyNormalizing := fun focusStronglyNormalizing =>
          natElim_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
            focusStronglyNormalizing motiveStronglyNormalizing (candidateMembersSN zeroBranchMember)
            succBranchStronglyNormalizing)
        (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeNatElim focusWeakHead)
        (spineNeutral := fun focusNeutral => IsNeutral.natElim focusNeutral)
        (headExpand := headExpand)
        (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
        (valueHandler := valueHandler)
        (scrutineeMember := currentMember)
  -- The structured value the scrutinee reaches; recurse on its `IsNatStructured` derivation.
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    natStructuredMemberReachesStructuredValue scrutineeMember
  suffices aux : ∀ {structured : RawTerm scope}, IsNatStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsNatStructured currentScrutinee →
        StepStar currentScrutinee structured →
        resultCandidate (natElimCellSpine motive currentScrutinee zeroBranch succBranch) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
  clear scrutineeReachesValue scrutineeMember scrutinee structuredValue structuredValueIsStructured
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | zero =>
      intro currentScrutinee currentMember scrutineeReachesZero
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesZero : StepStar (natSuccCell predecessor) natZeroCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesZero rfl
        obtain ⟨_predecessorAfter, zeroEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesZero predecessor rfl
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator zeroEqualsSucc)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      intro currentScrutinee currentMember scrutineeReachesNeutral
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesNeutral : StepStar (natSuccCell predecessor) neutralTerm :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNeutral
            neutralTermIsNormal
        obtain ⟨_predecessorAfter, neutralEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesNeutral predecessor rfl
        exact (isNeutral_rootGenerator_ne_natSucc (neutralEqualsSucc ▸ neutralTermIsNeutral) rfl).elim
  | @succ valuePredecessor valuePredecessorIsStructured outerInductiveHypothesis =>
      intro currentScrutinee currentMember scrutineeReachesSucc
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesSucc : StepStar (natSuccCell predecessor) (natSuccCell valuePredecessor) :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesSucc
            (isNatStructured_impliesStepNormalForm (IsNatStructured.succ valuePredecessorIsStructured))
        obtain ⟨predecessorAfter, succEquation, predecessorReachesAfter⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesSucc predecessor rfl
        have predecessorAfterEqualsValue : predecessorAfter = valuePredecessor := by
          injection succEquation with _equationOne _equationTwo _equationThree childrenEquation
          injection childrenEquation with _scopeEquation _shiftEquation _restShiftsEquation predecessorEquation
          exact predecessorEquation.symm
        subst predecessorAfterEqualsValue
        have predecessorMember : dataTaitCandidate IsNatStructured predecessor :=
          natSuccStructuredMember_predecessor (memberClosedUnderStepStar scrutineeReachesFocus currentMember)
        have predecessorCellMember :
            resultCandidate (natElimCellSpine motive predecessor zeroBranch succBranch) :=
          outerInductiveHypothesis predecessorMember predecessorReachesAfter
        exact headExpand IotaHeadStep.iotaNatElimSucc.toWeakHeadStep
          (succBranchSubstClosed predecessorMember predecessorCellMember) cellStronglyNormalizing

/-- **Dependent `natRec` reducibility over a structural-candidate scrutinee** — the dependent-recursor twin of
`natElimDependentReducibleMember`.  Identical structure (the same structured-value recursion, trichotomy, shape
recovery, confluence realignment, and predecessor descent), with the `gen_natRec` cell former, the
`iotaNatRec{Zero,Succ}` reductions, `WeakHeadStep.scrutineeNatRec`, `IsNeutral.natRec`, and the `natRec` SN
helper. -/
theorem natRecDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (candidateMembersSN : ∀ {term : RawTerm scope}, resultCandidate term → IsStronglyNormalizing term)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch)
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (scope + 1)) (currentSucc : RawTerm (scope + 2))
        (predecessor currentZero : RawTerm scope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc))
    (succBranchSubstClosed : ∀ {predecessor : RawTerm scope},
        dataTaitCandidate IsNatStructured predecessor →
        resultCandidate (natRecCellSpine motive predecessor zeroBranch succBranch) →
        resultCandidate
          (RawTerm.subst
            (RawTermSubst.cons (natRecCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch))
    (scrutineeMember : dataTaitCandidate IsNatStructured scrutinee) :
    resultCandidate (natRecCellSpine motive scrutinee zeroBranch succBranch) := by
  have memberClosedUnderStepStar : ∀ {source target : RawTerm scope},
      StepStar source target → dataTaitCandidate IsNatStructured source →
      dataTaitCandidate IsNatStructured target := by
    intro source target chain
    induction chain with
    | refl _ => exact fun member => member
    | trans firstStep _restChain restInductiveHypothesis =>
        exact fun member => restInductiveHypothesis (member.closedUnderStep firstStep)
  have runDispatch : ∀ {currentScrutinee : RawTerm scope},
      dataTaitCandidate IsNatStructured currentScrutinee →
      (∀ {focus : RawTerm scope},
        (focus = natZeroCell ∨ ∃ predecessor : RawTerm scope, focus = natSuccCell predecessor) →
        StepStar currentScrutinee focus →
        IsStronglyNormalizing (natRecCellSpine motive focus zeroBranch succBranch) →
        resultCandidate (natRecCellSpine motive focus zeroBranch succBranch)) →
      resultCandidate (natRecCellSpine motive currentScrutinee zeroBranch succBranch) :=
    fun currentMember valueHandler =>
      dependentDataEliminatorMemberFromValueDispatch
        (isValue := fun focus => focus = natZeroCell ∨ ∃ predecessor : RawTerm scope, focus = natSuccCell predecessor)
        (scrutineeCandidate := dataTaitCandidate IsNatStructured)
        (elimSpine := fun focus => natRecCellSpine motive focus zeroBranch succBranch)
        (focusTrichotomy := fun member =>
          dataTaitFocusTrichotomyOfValueHeadOrNeutral
            (valueHead := fun generator =>
              generator = Generator.gen_natZero ∨ generator = Generator.gen_natSucc)
            isNatStructured_valueHeadOrNeutral
            (fun headDisjunction =>
              headDisjunction.elim
                (fun zeroHead => Or.inl (eq_natZeroCell_of_rootGenerator zeroHead))
                (fun succHead => Or.inr (exists_predecessor_of_rootGenerator_natSucc succHead)))
            member)
        (candidateStronglyNormalizing := fun member => member.1)
        (candidateClosedUnderStep := fun member step => member.closedUnderStep step)
        (spineStronglyNormalizing := fun focusStronglyNormalizing =>
          natRec_isStronglyNormalizing_of_strongly_normalizing_branches succContractumTerminates
            focusStronglyNormalizing motiveStronglyNormalizing (candidateMembersSN zeroBranchMember)
            succBranchStronglyNormalizing)
        (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeNatRec focusWeakHead)
        (spineNeutral := fun focusNeutral => IsNeutral.natRec focusNeutral)
        (headExpand := headExpand)
        (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
        (valueHandler := valueHandler)
        (scrutineeMember := currentMember)
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    natStructuredMemberReachesStructuredValue scrutineeMember
  suffices aux : ∀ {structured : RawTerm scope}, IsNatStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsNatStructured currentScrutinee →
        StepStar currentScrutinee structured →
        resultCandidate (natRecCellSpine motive currentScrutinee zeroBranch succBranch) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
  clear scrutineeReachesValue scrutineeMember scrutinee structuredValue structuredValueIsStructured
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | zero =>
      intro currentScrutinee currentMember scrutineeReachesZero
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesZero : StepStar (natSuccCell predecessor) natZeroCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesZero rfl
        obtain ⟨_predecessorAfter, zeroEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesZero predecessor rfl
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator zeroEqualsSucc)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      intro currentScrutinee currentMember scrutineeReachesNeutral
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesNeutral : StepStar (natSuccCell predecessor) neutralTerm :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNeutral
            neutralTermIsNormal
        obtain ⟨_predecessorAfter, neutralEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesNeutral predecessor rfl
        exact (isNeutral_rootGenerator_ne_natSucc (neutralEqualsSucc ▸ neutralTermIsNeutral) rfl).elim
  | @succ valuePredecessor valuePredecessorIsStructured outerInductiveHypothesis =>
      intro currentScrutinee currentMember scrutineeReachesSucc
      refine runDispatch currentMember (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember cellStronglyNormalizing
      · subst focusEquation
        have focusReachesSucc : StepStar (natSuccCell predecessor) (natSuccCell valuePredecessor) :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesSucc
            (isNatStructured_impliesStepNormalForm (IsNatStructured.succ valuePredecessorIsStructured))
        obtain ⟨predecessorAfter, succEquation, predecessorReachesAfter⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesSucc predecessor rfl
        have predecessorAfterEqualsValue : predecessorAfter = valuePredecessor := by
          injection succEquation with _equationOne _equationTwo _equationThree childrenEquation
          injection childrenEquation with _scopeEquation _shiftEquation _restShiftsEquation predecessorEquation
          exact predecessorEquation.symm
        subst predecessorAfterEqualsValue
        have predecessorMember : dataTaitCandidate IsNatStructured predecessor :=
          natSuccStructuredMember_predecessor (memberClosedUnderStepStar scrutineeReachesFocus currentMember)
        have predecessorCellMember :
            resultCandidate (natRecCellSpine motive predecessor zeroBranch succBranch) :=
          outerInductiveHypothesis predecessorMember predecessorReachesAfter
        exact headExpand IotaHeadStep.iotaNatRecSucc.toWeakHeadStep
          (succBranchSubstClosed predecessorMember predecessorCellMember) cellStronglyNormalizing

end FX1Poly.Core
