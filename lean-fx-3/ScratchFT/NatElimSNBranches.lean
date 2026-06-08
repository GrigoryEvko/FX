import FX1Poly.Core.StrongNormalizationNatElim

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- The natElim succ-contractum `app (app succBranch predecessor) (natElim predecessor zeroBranch succBranch)`. -/
private abbrev natElimSuccContractum {scope : Nat} (succBranch predecessor zeroBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons
        (.mkGen .gen_natElim ()
          (.childCons predecessor (.childCons zeroBranch (.childCons succBranch .childNil))))
        .childNil))

/-- natElim SN from SN (not normal) branches: the succ-contractum SN hypothesis (for every SN predecessor) is
threaded through both branch inductions, updated under each branch-congruence via app/natElim congruence +
`IsStronglyNormalizing.inv` (the succ branch appears TWICE in the contractum, so its update is two hops). -/
theorem natElim_isStronglyNormalizing_of_strongly_normalizing_branches_probe {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (succContractumTerminates :
      ∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natElimSuccContractum succBranch predecessor zeroBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentZero currentSucc : RawTerm scope},
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
          (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
            IsStronglyNormalizing (natElimSuccContractum currentSucc predecessor currentZero)) →
          IsStronglyNormalizing
            (.mkGen .gen_natElim ()
              (.childCons currentScrutinee
                (.childCons currentZero (.childCons currentSucc .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentZero currentSucc currentZeroTerminates currentSuccTerminates currentSuccContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            ∀ {currentSucc : RawTerm scope},
              IsStronglyNormalizing currentSucc →
                (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                  IsStronglyNormalizing (natElimSuccContractum currentSucc predecessor innerZero)) →
                IsStronglyNormalizing
                  (.mkGen .gen_natElim ()
                    (.childCons currentScrutinee
                      (.childCons innerZero (.childCons currentSucc .childNil)))))
          (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
            intro currentSucc currentSuccTerminates currentInnerZeroContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                    IsStronglyNormalizing (natElimSuccContractum innerSucc predecessor currentInnerZero)) →
                    IsStronglyNormalizing
                      (.mkGen .gen_natElim ()
                        (.childCons currentScrutinee
                          (.childCons currentInnerZero (.childCons innerSucc .childNil)))))
                (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                      intro currentInnerSuccContractum
                      apply Acc.intro
                      intro targetTerm natElimStep
                      rcases Step.from_natElim natElimStep with
                        ⟨_scrutineeIsZero, targetIsZero⟩ |
                        ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                        ⟨succAfter, targetIsSuccStep, succStep⟩
                      · rw [targetIsZero]
                        exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                      · rw [targetIsContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsSucc] at currentScrutineeSN
                        exact currentInnerSuccContractum predecessor
                          (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          currentInnerSuccContractum
                      · rw [targetIsZeroStep]
                        refine zeroIH zeroAfter zeroStep
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          (fun predecessor predecessorTerminates => ?_)
                        -- update succContractum from currentInnerZero to zeroAfter (zb appears once, inside natElim)
                        exact (currentInnerSuccContractum predecessor predecessorTerminates).inv
                          (Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons currentInnerSucc (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natElim ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.here
                                      (.childCons currentInnerSucc .childNil : RawTermChildren [0] scope)
                                      zeroStep))))))
                      · rw [targetIsSuccStep]
                        refine succIH succAfter succStep (fun predecessor predecessorTerminates => ?_)
                        -- update succContractum from currentInnerSucc to succAfter (sb appears TWICE → two hops)
                        have hopOne :
                            Step (natElimSuccContractum currentInnerSucc predecessor currentInnerZero)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natElim ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil))) :=
                          Step.cong .gen_app ()
                            (StepChildren.here
                              (.childCons
                                (.mkGen .gen_natElim ()
                                  (.childCons predecessor
                                    (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                .childNil : RawTermChildren [0] scope)
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons predecessor .childNil : RawTermChildren [0] scope) succStep)))
                        have hopTwo :
                            Step
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natElim ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil)))
                              (natElimSuccContractum succAfter predecessor currentInnerZero) :=
                          Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons succAfter (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natElim ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.there (headShift := 0) currentInnerZero
                                      (StepChildren.here .childNil succStep))))))
                        exact (((currentInnerSuccContractum predecessor predecessorTerminates).inv hopOne).inv
                          hopTwo))
                currentSuccTerminates currentInnerZeroContractum)
          currentZeroTerminates currentSuccTerminates currentSuccContractum))
    scrutineeTerminates)
    zeroBranchTerminates succBranchTerminates succContractumTerminates

/-- The natRec succ-contractum `app (app succBranch predecessor) (natRec predecessor zeroBranch succBranch)`. -/
private abbrev natRecSuccContractum {scope : Nat} (succBranch predecessor zeroBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
      (.childCons
        (.mkGen .gen_natRec ()
          (.childCons predecessor (.childCons zeroBranch (.childCons succBranch .childNil))))
        .childNil))

theorem natRec_isStronglyNormalizing_of_strongly_normalizing_branches_probe {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    (succContractumTerminates :
      ∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
        IsStronglyNormalizing (natRecSuccContractum succBranch predecessor zeroBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (zeroBranchTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natRec ()
        (.childCons scrutinee (.childCons zeroBranch (.childCons succBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentZero currentSucc : RawTerm scope},
        IsStronglyNormalizing currentZero → IsStronglyNormalizing currentSucc →
          (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
            IsStronglyNormalizing (natRecSuccContractum currentSucc predecessor currentZero)) →
          IsStronglyNormalizing
            (.mkGen .gen_natRec ()
              (.childCons currentScrutinee
                (.childCons currentZero (.childCons currentSucc .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentZero currentSucc currentZeroTerminates currentSuccTerminates currentSuccContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerZero =>
            ∀ {currentSucc : RawTerm scope},
              IsStronglyNormalizing currentSucc →
                (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                  IsStronglyNormalizing (natRecSuccContractum currentSucc predecessor innerZero)) →
                IsStronglyNormalizing
                  (.mkGen .gen_natRec ()
                    (.childCons currentScrutinee
                      (.childCons innerZero (.childCons currentSucc .childNil)))))
          (m := fun currentInnerZero currentInnerZeroSuccessors zeroIH => by
            intro currentSucc currentSuccTerminates currentInnerZeroContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSucc =>
                  (∀ predecessor : RawTerm scope, IsStronglyNormalizing predecessor →
                    IsStronglyNormalizing (natRecSuccContractum innerSucc predecessor currentInnerZero)) →
                    IsStronglyNormalizing
                      (.mkGen .gen_natRec ()
                        (.childCons currentScrutinee
                          (.childCons currentInnerZero (.childCons innerSucc .childNil)))))
                (m := fun currentInnerSucc currentInnerSuccSuccessors succIH => by
                      intro currentInnerSuccContractum
                      apply Acc.intro
                      intro targetTerm natRecStep
                      rcases Step.from_natRec natRecStep with
                        ⟨_scrutineeIsZero, targetIsZero⟩ |
                        ⟨predecessor, scrutineeIsSucc, targetIsContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨zeroAfter, targetIsZeroStep, zeroStep⟩ |
                        ⟨succAfter, targetIsSuccStep, succStep⟩
                      · rw [targetIsZero]
                        exact Acc.intro currentInnerZero currentInnerZeroSuccessors
                      · rw [targetIsContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsSucc] at currentScrutineeSN
                        exact currentInnerSuccContractum predecessor
                          (predecessor_isStronglyNormalizing_of_natSucc currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerZero currentInnerZeroSuccessors)
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          currentInnerSuccContractum
                      · rw [targetIsZeroStep]
                        refine zeroIH zeroAfter zeroStep
                          (Acc.intro currentInnerSucc currentInnerSuccSuccessors)
                          (fun predecessor predecessorTerminates => ?_)
                        exact (currentInnerSuccContractum predecessor predecessorTerminates).inv
                          (Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons currentInnerSucc (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natRec ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.here
                                      (.childCons currentInnerSucc .childNil : RawTermChildren [0] scope)
                                      zeroStep))))))
                      · rw [targetIsSuccStep]
                        refine succIH succAfter succStep (fun predecessor predecessorTerminates => ?_)
                        have hopOne :
                            Step (natRecSuccContractum currentInnerSucc predecessor currentInnerZero)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natRec ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil))) :=
                          Step.cong .gen_app ()
                            (StepChildren.here
                              (.childCons
                                (.mkGen .gen_natRec ()
                                  (.childCons predecessor
                                    (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                .childNil : RawTermChildren [0] scope)
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons predecessor .childNil : RawTermChildren [0] scope) succStep)))
                        have hopTwo :
                            Step
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons succAfter (.childCons predecessor .childNil)))
                                  (.childCons
                                    (.mkGen .gen_natRec ()
                                      (.childCons predecessor
                                        (.childCons currentInnerZero (.childCons currentInnerSucc .childNil))))
                                    .childNil)))
                              (natRecSuccContractum succAfter predecessor currentInnerZero) :=
                          Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons succAfter (.childCons predecessor .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_natRec ()
                                  (StepChildren.there (headShift := 0) predecessor
                                    (StepChildren.there (headShift := 0) currentInnerZero
                                      (StepChildren.here .childNil succStep))))))
                        exact (((currentInnerSuccContractum predecessor predecessorTerminates).inv hopOne).inv
                          hopTwo))
                currentSuccTerminates currentInnerZeroContractum)
          currentZeroTerminates currentSuccTerminates currentSuccContractum))
    scrutineeTerminates)
    zeroBranchTerminates succBranchTerminates succContractumTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.StepStar.natElim_isStronglyNormalizing_of_strongly_normalizing_branches_probe
#print axioms FX1Poly.Core.StepStar.natRec_isStronglyNormalizing_of_strongly_normalizing_branches_probe
