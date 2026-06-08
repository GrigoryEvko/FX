import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

namespace FX1Poly.Core
namespace StepStar

-- 1-child value subterm-SN lemmas (mirror predecessor_isStronglyNormalizing_of_natSucc)
theorem value_isStronglyNormalizing_of_optionSome_probe {scope : Nat}
    {value : RawTerm scope}
    (someTerminates :
      IsStronglyNormalizing (.mkGen .gen_optionSome () (.childCons value .childNil) : RawTerm scope)) :
    IsStronglyNormalizing value := by
  suffices general :
      ∀ {someTerm : RawTerm scope}, Acc StepSuccessor someTerm →
        ∀ {currentValue : RawTerm scope},
          someTerm = .mkGen .gen_optionSome () (.childCons currentValue .childNil) →
          Acc StepSuccessor currentValue from
    general someTerminates rfl
  intro someTerm someAccessible
  induction someAccessible with
  | intro someWitness _somePredecessors someInductiveHypothesis =>
      intro currentValue witnessEq
      subst witnessEq
      apply Acc.intro
      intro valueAfter valueStep
      have congruenceLift :
          Step (.mkGen .gen_optionSome () (.childCons currentValue .childNil) : RawTerm scope)
            (.mkGen .gen_optionSome () (.childCons valueAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_optionSome () (StepChildren.here .childNil valueStep)
      exact someInductiveHypothesis
        (.mkGen .gen_optionSome () (.childCons valueAfter .childNil)) congruenceLift rfl

theorem value_isStronglyNormalizing_of_eitherInl_probe {scope : Nat}
    {value : RawTerm scope}
    (inlTerminates :
      IsStronglyNormalizing (.mkGen .gen_eitherInl () (.childCons value .childNil) : RawTerm scope)) :
    IsStronglyNormalizing value := by
  suffices general :
      ∀ {inlTerm : RawTerm scope}, Acc StepSuccessor inlTerm →
        ∀ {currentValue : RawTerm scope},
          inlTerm = .mkGen .gen_eitherInl () (.childCons currentValue .childNil) →
          Acc StepSuccessor currentValue from
    general inlTerminates rfl
  intro inlTerm inlAccessible
  induction inlAccessible with
  | intro inlWitness _inlPredecessors inlInductiveHypothesis =>
      intro currentValue witnessEq
      subst witnessEq
      apply Acc.intro
      intro valueAfter valueStep
      have congruenceLift :
          Step (.mkGen .gen_eitherInl () (.childCons currentValue .childNil) : RawTerm scope)
            (.mkGen .gen_eitherInl () (.childCons valueAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_eitherInl () (StepChildren.here .childNil valueStep)
      exact inlInductiveHypothesis
        (.mkGen .gen_eitherInl () (.childCons valueAfter .childNil)) congruenceLift rfl

theorem value_isStronglyNormalizing_of_eitherInr_probe {scope : Nat}
    {value : RawTerm scope}
    (inrTerminates :
      IsStronglyNormalizing (.mkGen .gen_eitherInr () (.childCons value .childNil) : RawTerm scope)) :
    IsStronglyNormalizing value := by
  suffices general :
      ∀ {inrTerm : RawTerm scope}, Acc StepSuccessor inrTerm →
        ∀ {currentValue : RawTerm scope},
          inrTerm = .mkGen .gen_eitherInr () (.childCons currentValue .childNil) →
          Acc StepSuccessor currentValue from
    general inrTerminates rfl
  intro inrTerm inrAccessible
  induction inrAccessible with
  | intro inrWitness _inrPredecessors inrInductiveHypothesis =>
      intro currentValue witnessEq
      subst witnessEq
      apply Acc.intro
      intro valueAfter valueStep
      have congruenceLift :
          Step (.mkGen .gen_eitherInr () (.childCons currentValue .childNil) : RawTerm scope)
            (.mkGen .gen_eitherInr () (.childCons valueAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_eitherInr () (StepChildren.here .childNil valueStep)
      exact inrInductiveHypothesis
        (.mkGen .gen_eitherInr () (.childCons valueAfter .childNil)) congruenceLift rfl

-- optionMatch firing-case SN (none passive + some applied-contractum hypothesis)
theorem optionMatch_isStronglyNormalizing_of_normal_branches_probe {scope : Nat}
    {scrutinee noneBranch someBranch : RawTerm scope}
    (noneBranchHasNoStep : ∀ targetNone : RawTerm scope, Step noneBranch targetNone → False)
    (someBranchHasNoStep : ∀ targetSome : RawTerm scope, Step someBranch targetSome → False)
    (someContractumTerminates :
      ∀ {value : RawTerm scope}, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_optionMatch ()
        (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_optionMatch ()
          (.childCons currentScrutinee
            (.childCons noneBranch (.childCons someBranch .childNil))) : RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_optionMatch ()
          (.childCons currentScrutinee
            (.childCons noneBranch (.childCons someBranch .childNil))) : RawTerm scope)
        (fun targetTerm matchStep => by
          rcases Step.from_optionMatch matchStep with
            ⟨_scrutineeIsNone, targetIsNone⟩ |
            ⟨value, scrutineeIsSome, targetIsContractum⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
            ⟨noneAfter, _targetIsNoneStep, noneStep⟩ |
            ⟨someAfter, _targetIsSomeStep, someStep⟩
          · rw [targetIsNone]
            exact isStronglyNormalizing_of_noStep noneBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsSome] at currentScrutineeSN
            exact someContractumTerminates
              (value_isStronglyNormalizing_of_optionSome_probe currentScrutineeSN)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep
          · exact absurd noneStep (noneBranchHasNoStep noneAfter)
          · exact absurd someStep (someBranchHasNoStep someAfter)))
    scrutineeTerminates

-- eitherMatch firing-case SN (both arms applied-contractum hypotheses)
theorem eitherMatch_isStronglyNormalizing_of_normal_branches_probe {scope : Nat}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    (leftBranchHasNoStep : ∀ targetLeft : RawTerm scope, Step leftBranch targetLeft → False)
    (rightBranchHasNoStep : ∀ targetRight : RawTerm scope, Step rightBranch targetRight → False)
    (leftContractumTerminates :
      ∀ {value : RawTerm scope}, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)) : RawTerm scope))
    (rightContractumTerminates :
      ∀ {value : RawTerm scope}, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherMatch ()
        (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_eitherMatch ()
          (.childCons currentScrutinee
            (.childCons leftBranch (.childCons rightBranch .childNil))) : RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_eitherMatch ()
          (.childCons currentScrutinee
            (.childCons leftBranch (.childCons rightBranch .childNil))) : RawTerm scope)
        (fun targetTerm matchStep => by
          rcases Step.from_eitherMatch matchStep with
            ⟨value, scrutineeIsInl, targetIsLeftContractum⟩ |
            ⟨value, scrutineeIsInr, targetIsRightContractum⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
            ⟨leftAfter, _targetIsLeftStep, leftStep⟩ |
            ⟨rightAfter, _targetIsRightStep, rightStep⟩
          · rw [targetIsLeftContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsInl] at currentScrutineeSN
            exact leftContractumTerminates
              (value_isStronglyNormalizing_of_eitherInl_probe currentScrutineeSN)
          · rw [targetIsRightContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsInr] at currentScrutineeSN
            exact rightContractumTerminates
              (value_isStronglyNormalizing_of_eitherInr_probe currentScrutineeSN)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep
          · exact absurd leftStep (leftBranchHasNoStep leftAfter)
          · exact absurd rightStep (rightBranchHasNoStep rightAfter)))
    scrutineeTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_optionSome_probe
#print axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_eitherInl_probe
#print axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_eitherInr_probe
#print axioms FX1Poly.Core.StepStar.optionMatch_isStronglyNormalizing_of_normal_branches_probe
#print axioms FX1Poly.Core.StepStar.eitherMatch_isStronglyNormalizing_of_normal_branches_probe
