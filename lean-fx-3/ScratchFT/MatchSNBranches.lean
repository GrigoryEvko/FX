import FX1Poly.Core.StrongNormalizationMatch

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- optionMatch SN from SN (not normal) branches: the some-contractum `app someBranch value` SN for every SN
value is threaded through the someBranch induction (updated under someBranch-congruence via app-cong + SN.inv). -/
theorem optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches_probe {scope : Nat}
    {scrutinee noneBranch someBranch : RawTerm scope}
    (someContractumTerminates :
      ∀ value : RawTerm scope, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil))))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (noneBranchTerminates : IsStronglyNormalizing noneBranch)
    (someBranchTerminates : IsStronglyNormalizing someBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_optionMatch ()
        (.childCons scrutinee (.childCons noneBranch (.childCons someBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentNone currentSome : RawTerm scope},
        IsStronglyNormalizing currentNone → IsStronglyNormalizing currentSome →
          (∀ value : RawTerm scope, IsStronglyNormalizing value →
            IsStronglyNormalizing
              (.mkGen .gen_app () (.childCons currentSome (.childCons value .childNil)))) →
          IsStronglyNormalizing
            (.mkGen .gen_optionMatch ()
              (.childCons currentScrutinee
                (.childCons currentNone (.childCons currentSome .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentNone currentSome currentNoneTerminates currentSomeTerminates currentSomeContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerNone =>
            ∀ {innerSome : RawTerm scope},
              IsStronglyNormalizing innerSome →
                (∀ value : RawTerm scope, IsStronglyNormalizing value →
                  IsStronglyNormalizing
                    (.mkGen .gen_app () (.childCons innerSome (.childCons value .childNil)))) →
                IsStronglyNormalizing
                  (.mkGen .gen_optionMatch ()
                    (.childCons currentScrutinee
                      (.childCons innerNone (.childCons innerSome .childNil)))))
          (m := fun currentInnerNone currentInnerNoneSuccessors noneIH => by
            intro innerSome innerSomeTerminates innerSomeContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSome' =>
                  (∀ value : RawTerm scope, IsStronglyNormalizing value →
                    IsStronglyNormalizing
                      (.mkGen .gen_app () (.childCons innerSome' (.childCons value .childNil)))) →
                    IsStronglyNormalizing
                      (.mkGen .gen_optionMatch ()
                        (.childCons currentScrutinee
                          (.childCons currentInnerNone (.childCons innerSome' .childNil)))))
                (m := fun currentInnerSome currentInnerSomeSuccessors someIH => by
                      intro currentInnerSomeContractum
                      apply Acc.intro
                      intro targetTerm matchStep
                      rcases Step.from_optionMatch matchStep with
                        ⟨_scrutineeIsNone, targetIsNone⟩ |
                        ⟨value, scrutineeIsSome, targetIsContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨noneAfter, targetIsNoneStep, noneStep⟩ |
                        ⟨someAfter, targetIsSomeStep, someStep⟩
                      · rw [targetIsNone]
                        exact Acc.intro currentInnerNone currentInnerNoneSuccessors
                      · rw [targetIsContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsSome] at currentScrutineeSN
                        exact currentInnerSomeContractum value
                          (value_isStronglyNormalizing_of_optionSome currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerNone currentInnerNoneSuccessors)
                          (Acc.intro currentInnerSome currentInnerSomeSuccessors)
                          currentInnerSomeContractum
                      · rw [targetIsNoneStep]
                        exact noneIH noneAfter noneStep
                          (Acc.intro currentInnerSome currentInnerSomeSuccessors)
                          currentInnerSomeContractum
                      · rw [targetIsSomeStep]
                        exact someIH someAfter someStep
                          (fun value valueTerminates =>
                            (currentInnerSomeContractum value valueTerminates).inv
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons value .childNil : RawTermChildren [0] scope)
                                  someStep))))
                innerSomeTerminates innerSomeContractum)
          currentNoneTerminates currentSomeTerminates currentSomeContractum))
    scrutineeTerminates)
    noneBranchTerminates someBranchTerminates someContractumTerminates

/-- eitherMatch SN from SN branches: BOTH the left- and right-contractum SN hypotheses are threaded (left
through the leftBranch induction, right through the rightBranch induction), updated under their congruences. -/
theorem eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches_probe {scope : Nat}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    (leftContractumTerminates :
      ∀ value : RawTerm scope, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil))))
    (rightContractumTerminates :
      ∀ value : RawTerm scope, IsStronglyNormalizing value →
        IsStronglyNormalizing
          (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil))))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (leftBranchTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchTerminates : IsStronglyNormalizing rightBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherMatch ()
        (.childCons scrutinee (.childCons leftBranch (.childCons rightBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentLeft currentRight : RawTerm scope},
        IsStronglyNormalizing currentLeft → IsStronglyNormalizing currentRight →
          (∀ value : RawTerm scope, IsStronglyNormalizing value →
            IsStronglyNormalizing
              (.mkGen .gen_app () (.childCons currentLeft (.childCons value .childNil)))) →
          (∀ value : RawTerm scope, IsStronglyNormalizing value →
            IsStronglyNormalizing
              (.mkGen .gen_app () (.childCons currentRight (.childCons value .childNil)))) →
          IsStronglyNormalizing
            (.mkGen .gen_eitherMatch ()
              (.childCons currentScrutinee
                (.childCons currentLeft (.childCons currentRight .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentLeft currentRight currentLeftTerminates currentRightTerminates
        currentLeftContractum currentRightContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerLeft =>
            ∀ {currentRight : RawTerm scope},
              IsStronglyNormalizing currentRight →
                (∀ value : RawTerm scope, IsStronglyNormalizing value →
                  IsStronglyNormalizing
                    (.mkGen .gen_app () (.childCons innerLeft (.childCons value .childNil)))) →
                (∀ value : RawTerm scope, IsStronglyNormalizing value →
                  IsStronglyNormalizing
                    (.mkGen .gen_app () (.childCons currentRight (.childCons value .childNil)))) →
                IsStronglyNormalizing
                  (.mkGen .gen_eitherMatch ()
                    (.childCons currentScrutinee
                      (.childCons innerLeft (.childCons currentRight .childNil)))))
          (m := fun currentInnerLeft currentInnerLeftSuccessors leftIH => by
            intro currentRight currentRightTerminates currentInnerLeftContractum
              currentRightContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerRight =>
                  (∀ value : RawTerm scope, IsStronglyNormalizing value →
                    IsStronglyNormalizing
                      (.mkGen .gen_app ()
                        (.childCons currentInnerLeft (.childCons value .childNil)))) →
                    (∀ value : RawTerm scope, IsStronglyNormalizing value →
                      IsStronglyNormalizing
                        (.mkGen .gen_app () (.childCons innerRight (.childCons value .childNil)))) →
                      IsStronglyNormalizing
                        (.mkGen .gen_eitherMatch ()
                          (.childCons currentScrutinee
                            (.childCons currentInnerLeft (.childCons innerRight .childNil)))))
                (m := fun currentInnerRight currentInnerRightSuccessors rightIH => by
                      intro currentInnerLeftContractum' currentInnerRightContractum
                      apply Acc.intro
                      intro targetTerm matchStep
                      rcases Step.from_eitherMatch matchStep with
                        ⟨value, scrutineeIsInl, targetIsLeftContractum⟩ |
                        ⟨value, scrutineeIsInr, targetIsRightContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨leftAfter, targetIsLeftStep, leftStep⟩ |
                        ⟨rightAfter, targetIsRightStep, rightStep⟩
                      · rw [targetIsLeftContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsInl] at currentScrutineeSN
                        exact currentInnerLeftContractum' value
                          (value_isStronglyNormalizing_of_eitherInl currentScrutineeSN)
                      · rw [targetIsRightContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsInr] at currentScrutineeSN
                        exact currentInnerRightContractum value
                          (value_isStronglyNormalizing_of_eitherInr currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerLeft currentInnerLeftSuccessors)
                          (Acc.intro currentInnerRight currentInnerRightSuccessors)
                          currentInnerLeftContractum' currentInnerRightContractum
                      · rw [targetIsLeftStep]
                        exact leftIH leftAfter leftStep
                          (Acc.intro currentInnerRight currentInnerRightSuccessors)
                          (fun value valueTerminates =>
                            (currentInnerLeftContractum' value valueTerminates).inv
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons value .childNil : RawTermChildren [0] scope)
                                  leftStep)))
                          currentInnerRightContractum
                      · rw [targetIsRightStep]
                        exact rightIH rightAfter rightStep
                          currentInnerLeftContractum'
                          (fun value valueTerminates =>
                            (currentInnerRightContractum value valueTerminates).inv
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons value .childNil : RawTermChildren [0] scope)
                                  rightStep))))
                currentRightTerminates currentInnerLeftContractum currentRightContractum)
          currentLeftTerminates currentRightTerminates currentLeftContractum
            currentRightContractum))
    scrutineeTerminates)
    leftBranchTerminates rightBranchTerminates leftContractumTerminates rightContractumTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.StepStar.optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches_probe
#print axioms FX1Poly.Core.StepStar.eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches_probe
