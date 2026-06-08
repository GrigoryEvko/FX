import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

namespace FX1Poly.Core
namespace StepStar

-- Part 1: subterm-SN lemma (pred SN from natSucc pred SN), parallel to firstComponent_of_pair (1-child)
theorem predecessor_isStronglyNormalizing_of_natSucc_probe {scope : Nat}
    {predecessor : RawTerm scope}
    (succTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_natSucc () (.childCons predecessor .childNil) : RawTerm scope)) :
    IsStronglyNormalizing predecessor := by
  suffices general :
      ∀ {succTerm : RawTerm scope}, Acc StepSuccessor succTerm →
        ∀ {currentPred : RawTerm scope},
          succTerm = .mkGen .gen_natSucc () (.childCons currentPred .childNil) →
          Acc StepSuccessor currentPred from
    general succTerminates rfl
  intro succTerm succAccessible
  induction succAccessible with
  | intro succWitness _succPredecessors succInductiveHypothesis =>
      intro currentPred witnessEq
      subst witnessEq
      apply Acc.intro
      intro predAfter predStep
      have congruenceLift :
          Step
            (.mkGen .gen_natSucc () (.childCons currentPred .childNil) : RawTerm scope)
            (.mkGen .gen_natSucc () (.childCons predAfter .childNil) : RawTerm scope) :=
        Step.cong .gen_natSucc () (StepChildren.here .childNil predStep)
      exact succInductiveHypothesis
        (.mkGen .gen_natSucc () (.childCons predAfter .childNil))
        congruenceLift rfl

-- Part 2: conditional natElim-succ iota-redex SN (normal branches + succ-contractum hypothesis)
theorem natElim_isStronglyNormalizing_of_normal_branches_probe {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (zeroBranchHasNoStep : ∀ targetZero : RawTerm scope, Step zeroBranch targetZero → False)
    (succBranchHasNoStep : ∀ targetSucc : RawTerm scope, Step succBranch targetSucc → False)
    (succContractumTerminates :
      ∀ {predecessor : RawTerm scope}, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons
                (.mkGen .gen_natElim ()
                  (.childCons predecessor
                    (.childCons zeroBranch (.childCons succBranch .childNil))))
                .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_natElim ()
          (.childCons currentScrutinee
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_natElim ()
          (.childCons currentScrutinee
            (.childCons zeroBranch (.childCons succBranch .childNil))) :
          RawTerm scope)
        (fun targetTerm natElimStep => by
          rcases Step.from_natElim natElimStep with
            ⟨_scrutineeIsZero, targetIsZero⟩ |
            ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
            ⟨zeroAfter, _targetIsZeroStep, zeroStep⟩ |
            ⟨succAfter, _targetIsSuccStep, succStep⟩
          · rw [targetIsZero]
            exact isStronglyNormalizing_of_noStep zeroBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsSucc] at currentScrutineeSN
            exact succContractumTerminates
              (predecessor_isStronglyNormalizing_of_natSucc_probe currentScrutineeSN)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep
          · exact absurd zeroStep (zeroBranchHasNoStep zeroAfter)
          · exact absurd succStep (succBranchHasNoStep succAfter)))
    scrutineeTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.StepStar.predecessor_isStronglyNormalizing_of_natSucc_probe
#print axioms FX1Poly.Core.StepStar.natElim_isStronglyNormalizing_of_normal_branches_probe
