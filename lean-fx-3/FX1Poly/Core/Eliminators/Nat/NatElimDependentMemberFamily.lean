import FX1Poly.Core.Eliminators.Nat.NatElimDependentMember

/-! # FX1Poly/Core/NatElimDependentMemberFamily
    — dependent `natElim` over a VALUE-INDEXED candidate family (the genuinely dependent recursor reducibility)

`natElimDependentReducibleMember` (the fixed-candidate keystone) proves the cell lands in a SINGLE
`resultCandidate`.  That is exactly right when the motive is non-dependent (every `subst0 motive v` shares one
candidate), but the genuinely DEPENDENT recursor needs more: the recursive cell at a predecessor has type
`subst0 motive predecessor`, NOT convertible to `subst0 motive scrutinee` (since `scrutinee ↠ natSucc(…pred…)`),
so the predecessor cell lives in a DIFFERENT candidate than the goal.  Bool escapes this (no recursion; its
conditional branches supply the value-conversion); nat's recursion does not.

The fix is a candidate FAMILY `resultCandidateAt : value → (RawTerm → Prop)` — the candidate of `subst0 motive
value` — reduction-stable (`StepStar v w → resultCandidateAt v ≈ resultCandidateAt w`, the Conv-invariance of the
result type's candidate along the scrutinee's reduction).  The structural recursion already tracks the structured
value at each level; this file threads the family through it, so the predecessor cell lands in
`resultCandidateAt predecessor` and the succ result in `resultCandidateAt (natSucc predecessor)` — both
type-correct.  The fixed keystone is the constant-family instance (`resultCandidateAt := fun _ => resultCandidate`,
stability `Iff.rfl`).

The bounded FT bridge instantiates `resultCandidateAt v := IsReducibleMemberAtBounded env bound (subst0 motive v)`
and discharges `candidateStable` from `subst0`-congruence + the bounded model's Conv-invariance.  The per-value
premises are gated on the value's structured membership (so the bridge only supplies them at reducible `v`, where
`subst0 motive v` is a reducible type).

## Zero-axiom verification

The same structural `induction` on `IsNatStructured` driving the shared `dependentDataEliminatorMemberFromValue\
Dispatch` per case (now at the case's value-indexed candidate), with the family's stability iff threaded at three
points (top reduction, the predecessor descent, the `natSucc` congruence) and the `natZero`-focus vacuity in the
neutral / succ cases discharged by confluence + `IsNeutral.rootGenerator_ne_natZero` / `Generator.noConfusion`.
No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core
open StepStar

/-- **Dependent `natElim` reducibility over a value-indexed candidate family.**  The genuinely-dependent
strengthening of `natElimDependentReducibleMember`: each scrutinee-value `v` carries its own result candidate
`resultCandidateAt v` (the motive at `v`), the family being reduction-stable; the recursive predecessor cell lands
in `resultCandidateAt predecessor`, the `succ`-ι reduct in `resultCandidateAt (natSucc predecessor)`. -/
theorem natElimDependentReducibleMemberFamily {scope : Nat}
    (resultCandidateAt : RawTerm scope → RawTerm scope → Prop)
    (candidateMembersSN : ∀ {value term : RawTerm scope}, dataTaitCandidate IsNatStructured value →
        resultCandidateAt value term → IsStronglyNormalizing term)
    (headExpand : ∀ {value redexTerm contractum : RawTerm scope}, dataTaitCandidate IsNatStructured value →
        WeakHeadStep redexTerm contractum → resultCandidateAt value contractum →
        IsStronglyNormalizing redexTerm → resultCandidateAt value redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {value neutralTerm : RawTerm scope},
        dataTaitCandidate IsNatStructured value →
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidateAt value neutralTerm)
    (candidateStable : ∀ {value valueReduct term : RawTerm scope},
        dataTaitCandidate IsNatStructured value → StepStar value valueReduct →
        (resultCandidateAt value term ↔ resultCandidateAt valueReduct term))
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (zeroBranchMember : resultCandidateAt natZeroCell zeroBranch)
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
        resultCandidateAt predecessor (natElimCellSpine motive predecessor zeroBranch succBranch) →
        resultCandidateAt (natSuccCell predecessor)
          (RawTerm.subst
            (RawTermSubst.cons (natElimCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch))
    (scrutineeMember : dataTaitCandidate IsNatStructured scrutinee) :
    resultCandidateAt scrutinee (natElimCellSpine motive scrutinee zeroBranch succBranch) := by
  -- Forward closure of the structural candidate along a whole reduction (CR2 iterated).
  have memberClosedUnderStepStar : ∀ {source target : RawTerm scope},
      StepStar source target → dataTaitCandidate IsNatStructured source →
      dataTaitCandidate IsNatStructured target := by
    intro source target chain
    induction chain with
    | refl _ => exact fun member => member
    | trans firstStep _restChain restInductiveHypothesis =>
        exact fun member => restInductiveHypothesis (member.closedUnderStep firstStep)
  -- The shared dispatch at the candidate of a FIXED structured value, parameterized by that value's structured
  -- membership (which the per-value `headExpand` / neutral closures need).  The scrutinee-side SN / closed-under-
  -- step are candidate-agnostic; only the result-candidate closures carry the value witness.
  have runDispatchAt : ∀ {structuredValue : RawTerm scope}, dataTaitCandidate IsNatStructured structuredValue →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsNatStructured currentScrutinee →
      (∀ {focus : RawTerm scope},
        (focus = natZeroCell ∨ ∃ predecessor : RawTerm scope, focus = natSuccCell predecessor) →
        StepStar currentScrutinee focus →
        IsStronglyNormalizing (natElimCellSpine motive focus zeroBranch succBranch) →
        resultCandidateAt structuredValue (natElimCellSpine motive focus zeroBranch succBranch)) →
      resultCandidateAt structuredValue (natElimCellSpine motive currentScrutinee zeroBranch succBranch) := by
    intro structuredValue structuredWitness currentScrutinee currentMember valueHandler
    exact dependentDataEliminatorMemberFromValueDispatch
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
            focusStronglyNormalizing motiveStronglyNormalizing
            (candidateMembersSN natZeroStructuredMember zeroBranchMember) succBranchStronglyNormalizing)
        (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeNatElim focusWeakHead)
        (spineNeutral := fun focusNeutral => IsNeutral.natElim focusNeutral)
        (headExpand := fun weakHeadStep contractumMember redexStronglyNormalizing =>
          headExpand structuredWitness weakHeadStep contractumMember redexStronglyNormalizing)
        (memberOfStronglyNormalizingNeutral := fun neutralStronglyNormalizing neutral =>
          memberOfStronglyNormalizingNeutral structuredWitness neutralStronglyNormalizing neutral)
        (valueHandler := valueHandler)
        (scrutineeMember := currentMember)
  -- The structured value the scrutinee reaches; recurse on its `IsNatStructured` derivation.  The aux conclusion is
  -- at the STRUCTURED value's candidate; the top closes back to the scrutinee's candidate by stability.
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    natStructuredMemberReachesStructuredValue scrutineeMember
  refine (candidateStable scrutineeMember scrutineeReachesValue).mpr ?_
  suffices aux : ∀ {structured : RawTerm scope}, IsNatStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsNatStructured currentScrutinee →
        StepStar currentScrutinee structured →
        resultCandidateAt structured (natElimCellSpine motive currentScrutinee zeroBranch succBranch) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
  clear scrutineeReachesValue scrutineeMember scrutinee structuredValue structuredValueIsStructured
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | zero =>
      intro currentScrutinee currentMember scrutineeReachesZero
      refine runDispatchAt natZeroStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand natZeroStructuredMember IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember
          cellStronglyNormalizing
      · subst focusEquation
        have focusReachesZero : StepStar (natSuccCell predecessor) natZeroCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesZero rfl
        obtain ⟨_predecessorAfter, zeroEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesZero predecessor rfl
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator zeroEqualsSucc)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      intro currentScrutinee currentMember scrutineeReachesNeutral
      have neutralStructuredMember : dataTaitCandidate IsNatStructured neutralTerm :=
        dataTaitCandidate.memberOfValue neutralTermIsNormal
          (IsNatStructured.neutralNormal neutralTermIsNeutral neutralTermIsNormal)
      refine runDispatchAt neutralStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        -- VACUOUS: the scrutinee reaches both `natZero` (focus) and the normal neutral `neutralTerm`.
        have neutralReachesZero : StepStar neutralTerm natZeroCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesNeutral scrutineeReachesFocus rfl
        have zeroEqualsNeutral : natZeroCell = neutralTerm :=
          StepStar.eq_of_noStep
            (fun reduct step =>
              RawTerm.isStepNormalForm_blocks_step neutralTermIsNormal reduct step) neutralReachesZero
        exact (IsNeutral.rootGenerator_ne_natZero (zeroEqualsNeutral ▸ neutralTermIsNeutral) rfl).elim
      · subst focusEquation
        have focusReachesNeutral : StepStar (natSuccCell predecessor) neutralTerm :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNeutral
            neutralTermIsNormal
        obtain ⟨_predecessorAfter, neutralEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesNeutral predecessor rfl
        exact (isNeutral_rootGenerator_ne_natSucc (neutralEqualsSucc ▸ neutralTermIsNeutral) rfl).elim
  | @succ valuePredecessor valuePredecessorIsStructured outerInductiveHypothesis =>
      intro currentScrutinee currentMember scrutineeReachesSucc
      have valuePredecessorMember : dataTaitCandidate IsNatStructured valuePredecessor :=
        dataTaitCandidate.memberOfValue (isNatStructured_impliesStepNormalForm valuePredecessorIsStructured)
          valuePredecessorIsStructured
      have succStructuredMember : dataTaitCandidate IsNatStructured (natSuccCell valuePredecessor) :=
        natSuccStructuredMember valuePredecessorMember
      refine runDispatchAt succStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        -- VACUOUS: the scrutinee reaches both `natZero` (focus) and the `natSucc` structured value.
        have zeroReachesSucc : StepStar natZeroCell (natSuccCell valuePredecessor) :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesSucc
            (isNatStructured_impliesStepNormalForm (IsNatStructured.succ valuePredecessorIsStructured))
        have succEqualsZero : natSuccCell valuePredecessor = natZeroCell :=
          StepStar.eq_of_noStep
            (fun reduct step =>
              RawTerm.isStepNormalForm_blocks_step
                (show RawTerm.isStepNormalForm (natZeroCell (scope := scope)) from rfl) reduct step)
            zeroReachesSucc
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator succEqualsZero)
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
        rw [predecessorAfterEqualsValue] at predecessorReachesAfter
        have predecessorMember : dataTaitCandidate IsNatStructured predecessor :=
          natSuccStructuredMember_predecessor (memberClosedUnderStepStar scrutineeReachesFocus currentMember)
        have predecessorCellMember :
            resultCandidateAt predecessor (natElimCellSpine motive predecessor zeroBranch succBranch) :=
          (candidateStable predecessorMember predecessorReachesAfter).mpr
            (outerInductiveHypothesis predecessorMember predecessorReachesAfter)
        have succReductMember :
            resultCandidateAt (natSuccCell valuePredecessor)
              (RawTerm.subst
                (RawTermSubst.cons (natElimCellSpine motive predecessor zeroBranch succBranch)
                  (RawTermSubst.singleton predecessor))
                succBranch) :=
          (candidateStable (natSuccStructuredMember predecessorMember) focusReachesSucc).mp
            (succBranchSubstClosed predecessorMember predecessorCellMember)
        exact headExpand succStructuredMember IotaHeadStep.iotaNatElimSucc.toWeakHeadStep succReductMember
          cellStronglyNormalizing

/-- **Dependent `natRec` reducibility over a value-indexed candidate family** — the dependent-recursor twin of
`natElimDependentReducibleMemberFamily`.  Identical structure (the structured-value recursion, the per-case
dispatch at the value-indexed candidate, the three stability conversions, the `natZero`-focus vacuity), with the
`gen_natRec` cell former, the `iotaNatRec{Zero,Succ}` reductions, `WeakHeadStep.scrutineeNatRec`,
`IsNeutral.natRec`, and the `natRec` SN helper. -/
theorem natRecDependentReducibleMemberFamily {scope : Nat}
    (resultCandidateAt : RawTerm scope → RawTerm scope → Prop)
    (candidateMembersSN : ∀ {value term : RawTerm scope}, dataTaitCandidate IsNatStructured value →
        resultCandidateAt value term → IsStronglyNormalizing term)
    (headExpand : ∀ {value redexTerm contractum : RawTerm scope}, dataTaitCandidate IsNatStructured value →
        WeakHeadStep redexTerm contractum → resultCandidateAt value contractum →
        IsStronglyNormalizing redexTerm → resultCandidateAt value redexTerm)
    (memberOfStronglyNormalizingNeutral : ∀ {value neutralTerm : RawTerm scope},
        dataTaitCandidate IsNatStructured value →
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidateAt value neutralTerm)
    (candidateStable : ∀ {value valueReduct term : RawTerm scope},
        dataTaitCandidate IsNatStructured value → StepStar value valueReduct →
        (resultCandidateAt value term ↔ resultCandidateAt valueReduct term))
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (zeroBranchMember : resultCandidateAt natZeroCell zeroBranch)
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
        resultCandidateAt predecessor (natRecCellSpine motive predecessor zeroBranch succBranch) →
        resultCandidateAt (natSuccCell predecessor)
          (RawTerm.subst
            (RawTermSubst.cons (natRecCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch))
    (scrutineeMember : dataTaitCandidate IsNatStructured scrutinee) :
    resultCandidateAt scrutinee (natRecCellSpine motive scrutinee zeroBranch succBranch) := by
  have memberClosedUnderStepStar : ∀ {source target : RawTerm scope},
      StepStar source target → dataTaitCandidate IsNatStructured source →
      dataTaitCandidate IsNatStructured target := by
    intro source target chain
    induction chain with
    | refl _ => exact fun member => member
    | trans firstStep _restChain restInductiveHypothesis =>
        exact fun member => restInductiveHypothesis (member.closedUnderStep firstStep)
  have runDispatchAt : ∀ {structuredValue : RawTerm scope}, dataTaitCandidate IsNatStructured structuredValue →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsNatStructured currentScrutinee →
      (∀ {focus : RawTerm scope},
        (focus = natZeroCell ∨ ∃ predecessor : RawTerm scope, focus = natSuccCell predecessor) →
        StepStar currentScrutinee focus →
        IsStronglyNormalizing (natRecCellSpine motive focus zeroBranch succBranch) →
        resultCandidateAt structuredValue (natRecCellSpine motive focus zeroBranch succBranch)) →
      resultCandidateAt structuredValue (natRecCellSpine motive currentScrutinee zeroBranch succBranch) := by
    intro structuredValue structuredWitness currentScrutinee currentMember valueHandler
    exact dependentDataEliminatorMemberFromValueDispatch
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
            focusStronglyNormalizing motiveStronglyNormalizing
            (candidateMembersSN natZeroStructuredMember zeroBranchMember) succBranchStronglyNormalizing)
        (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeNatRec focusWeakHead)
        (spineNeutral := fun focusNeutral => IsNeutral.natRec focusNeutral)
        (headExpand := fun weakHeadStep contractumMember redexStronglyNormalizing =>
          headExpand structuredWitness weakHeadStep contractumMember redexStronglyNormalizing)
        (memberOfStronglyNormalizingNeutral := fun neutralStronglyNormalizing neutral =>
          memberOfStronglyNormalizingNeutral structuredWitness neutralStronglyNormalizing neutral)
        (valueHandler := valueHandler)
        (scrutineeMember := currentMember)
  obtain ⟨structuredValue, scrutineeReachesValue, structuredValueIsStructured⟩ :=
    natStructuredMemberReachesStructuredValue scrutineeMember
  refine (candidateStable scrutineeMember scrutineeReachesValue).mpr ?_
  suffices aux : ∀ {structured : RawTerm scope}, IsNatStructured structured →
      ∀ {currentScrutinee : RawTerm scope}, dataTaitCandidate IsNatStructured currentScrutinee →
        StepStar currentScrutinee structured →
        resultCandidateAt structured (natRecCellSpine motive currentScrutinee zeroBranch succBranch) from
    aux structuredValueIsStructured scrutineeMember scrutineeReachesValue
  clear scrutineeReachesValue scrutineeMember scrutinee structuredValue structuredValueIsStructured
  intro structured structuredIsStructured
  induction structuredIsStructured with
  | zero =>
      intro currentScrutinee currentMember scrutineeReachesZero
      refine runDispatchAt natZeroStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        exact headExpand natZeroStructuredMember IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember
          cellStronglyNormalizing
      · subst focusEquation
        have focusReachesZero : StepStar (natSuccCell predecessor) natZeroCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesZero rfl
        obtain ⟨_predecessorAfter, zeroEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesZero predecessor rfl
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator zeroEqualsSucc)
  | @neutralNormal neutralTerm neutralTermIsNeutral neutralTermIsNormal =>
      intro currentScrutinee currentMember scrutineeReachesNeutral
      have neutralStructuredMember : dataTaitCandidate IsNatStructured neutralTerm :=
        dataTaitCandidate.memberOfValue neutralTermIsNormal
          (IsNatStructured.neutralNormal neutralTermIsNeutral neutralTermIsNormal)
      refine runDispatchAt neutralStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        have neutralReachesZero : StepStar neutralTerm natZeroCell :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesNeutral scrutineeReachesFocus rfl
        have zeroEqualsNeutral : natZeroCell = neutralTerm :=
          StepStar.eq_of_noStep
            (fun reduct step =>
              RawTerm.isStepNormalForm_blocks_step neutralTermIsNormal reduct step) neutralReachesZero
        exact (IsNeutral.rootGenerator_ne_natZero (zeroEqualsNeutral ▸ neutralTermIsNeutral) rfl).elim
      · subst focusEquation
        have focusReachesNeutral : StepStar (natSuccCell predecessor) neutralTerm :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesNeutral
            neutralTermIsNormal
        obtain ⟨_predecessorAfter, neutralEqualsSucc, _⟩ :=
          stepStar_under_unaryCell natSuccCell Step.from_natSucc focusReachesNeutral predecessor rfl
        exact (isNeutral_rootGenerator_ne_natSucc (neutralEqualsSucc ▸ neutralTermIsNeutral) rfl).elim
  | @succ valuePredecessor valuePredecessorIsStructured outerInductiveHypothesis =>
      intro currentScrutinee currentMember scrutineeReachesSucc
      have valuePredecessorMember : dataTaitCandidate IsNatStructured valuePredecessor :=
        dataTaitCandidate.memberOfValue (isNatStructured_impliesStepNormalForm valuePredecessorIsStructured)
          valuePredecessorIsStructured
      have succStructuredMember : dataTaitCandidate IsNatStructured (natSuccCell valuePredecessor) :=
        natSuccStructuredMember valuePredecessorMember
      refine runDispatchAt succStructuredMember currentMember
        (fun focusIsValue scrutineeReachesFocus cellStronglyNormalizing => ?_)
      rcases focusIsValue with focusEquation | ⟨predecessor, focusEquation⟩
      · subst focusEquation
        have zeroReachesSucc : StepStar natZeroCell (natSuccCell valuePredecessor) :=
          stepStar_focus_reaches_normal_target currentMember.1 scrutineeReachesFocus scrutineeReachesSucc
            (isNatStructured_impliesStepNormalForm (IsNatStructured.succ valuePredecessorIsStructured))
        have succEqualsZero : natSuccCell valuePredecessor = natZeroCell :=
          StepStar.eq_of_noStep
            (fun reduct step =>
              RawTerm.isStepNormalForm_blocks_step
                (show RawTerm.isStepNormalForm (natZeroCell (scope := scope)) from rfl) reduct step)
            zeroReachesSucc
        exact Generator.noConfusion (congrArg RawTerm.rootGenerator succEqualsZero)
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
        rw [predecessorAfterEqualsValue] at predecessorReachesAfter
        have predecessorMember : dataTaitCandidate IsNatStructured predecessor :=
          natSuccStructuredMember_predecessor (memberClosedUnderStepStar scrutineeReachesFocus currentMember)
        have predecessorCellMember :
            resultCandidateAt predecessor (natRecCellSpine motive predecessor zeroBranch succBranch) :=
          (candidateStable predecessorMember predecessorReachesAfter).mpr
            (outerInductiveHypothesis predecessorMember predecessorReachesAfter)
        have succReductMember :
            resultCandidateAt (natSuccCell valuePredecessor)
              (RawTerm.subst
                (RawTermSubst.cons (natRecCellSpine motive predecessor zeroBranch succBranch)
                  (RawTermSubst.singleton predecessor))
                succBranch) :=
          (candidateStable (natSuccStructuredMember predecessorMember) focusReachesSucc).mp
            (succBranchSubstClosed predecessorMember predecessorCellMember)
        exact headExpand succStructuredMember IotaHeadStep.iotaNatRecSucc.toWeakHeadStep succReductMember
          cellStronglyNormalizing

end FX1Poly.Core
