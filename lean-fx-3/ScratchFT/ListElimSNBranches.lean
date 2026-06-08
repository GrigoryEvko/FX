import FX1Poly.Core.StrongNormalizationListElim

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- The listElim cons-contractum `app (app (app consBranch head) tail) (listElim tail nilBranch consBranch)`. -/
private abbrev listElimConsContractum {scope : Nat} (consBranch head tail nilBranch : RawTerm scope) :
    RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (.mkGen .gen_listElim ()
          (.childCons tail (.childCons nilBranch (.childCons consBranch .childNil))))
        .childNil))

theorem listElim_isStronglyNormalizing_of_strongly_normalizing_branches_probe {scope : Nat}
    {scrutinee nilBranch consBranch : RawTerm scope}
    (consContractumTerminates :
      ∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractum consBranch head tail nilBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (nilBranchTerminates : IsStronglyNormalizing nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil)))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentNil currentCons : RawTerm scope},
        IsStronglyNormalizing currentNil → IsStronglyNormalizing currentCons →
          (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
            IsStronglyNormalizing (listElimConsContractum currentCons head tail currentNil)) →
          IsStronglyNormalizing
            (.mkGen .gen_listElim ()
              (.childCons currentScrutinee
                (.childCons currentNil (.childCons currentCons .childNil)))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentNil currentCons currentNilTerminates currentConsTerminates currentConsContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerNil =>
            ∀ {currentCons : RawTerm scope},
              IsStronglyNormalizing currentCons →
                (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
                  IsStronglyNormalizing (listElimConsContractum currentCons head tail innerNil)) →
                IsStronglyNormalizing
                  (.mkGen .gen_listElim ()
                    (.childCons currentScrutinee
                      (.childCons innerNil (.childCons currentCons .childNil)))))
          (m := fun currentInnerNil currentInnerNilSuccessors nilIH => by
            intro currentCons currentConsTerminates currentInnerNilContractum
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerCons =>
                  (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
                    IsStronglyNormalizing (listElimConsContractum innerCons head tail currentInnerNil)) →
                    IsStronglyNormalizing
                      (.mkGen .gen_listElim ()
                        (.childCons currentScrutinee
                          (.childCons currentInnerNil (.childCons innerCons .childNil)))))
                (m := fun currentInnerCons currentInnerConsSuccessors consIH => by
                      intro currentInnerConsContractum
                      apply Acc.intro
                      intro targetTerm listElimStep
                      rcases Step.from_listElim listElimStep with
                        ⟨_scrutineeIsNil, targetIsNil⟩ |
                        ⟨headValue, tailValue, scrutineeIsCons, targetIsContractum⟩ |
                        ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩ |
                        ⟨nilAfter, targetIsNilStep, nilStep⟩ |
                        ⟨consAfter, targetIsConsStep, consStep⟩
                      · rw [targetIsNil]
                        exact Acc.intro currentInnerNil currentInnerNilSuccessors
                      · rw [targetIsContractum]
                        have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                          Acc.intro currentScrutinee currentScrutineeSuccessors
                        rw [scrutineeIsCons] at currentScrutineeSN
                        exact currentInnerConsContractum headValue tailValue
                          (headValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
                          (tailValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
                      · rw [targetIsScrutineeStep]
                        exact scrutineeIH scrutineeAfter scrutineeStep
                          (Acc.intro currentInnerNil currentInnerNilSuccessors)
                          (Acc.intro currentInnerCons currentInnerConsSuccessors)
                          currentInnerConsContractum
                      · rw [targetIsNilStep]
                        refine nilIH nilAfter nilStep
                          (Acc.intro currentInnerCons currentInnerConsSuccessors)
                          (fun head tail headTerminates tailTerminates => ?_)
                        -- nilBranch occurs once, inside the recursive listElim (its second child)
                        exact (currentInnerConsContractum head tail headTerminates tailTerminates).inv
                          (Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app () (.childCons currentInnerCons (.childCons head .childNil)))
                                  (.childCons tail .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_listElim ()
                                  (StepChildren.there (headShift := 0) tail
                                    (StepChildren.here
                                      (.childCons currentInnerCons .childNil : RawTermChildren [0] scope)
                                      nilStep))))))
                      · rw [targetIsConsStep]
                        refine consIH consAfter consStep (fun head tail headTerminates tailTerminates => ?_)
                        -- consBranch occurs twice: in (app (app cb head) tail) and in the recursive listElim
                        have hopOne :
                            Step (listElimConsContractum currentInnerCons head tail currentInnerNil)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons
                                      (.mkGen .gen_app () (.childCons consAfter (.childCons head .childNil)))
                                      (.childCons tail .childNil)))
                                  (.childCons
                                    (.mkGen .gen_listElim ()
                                      (.childCons tail
                                        (.childCons currentInnerNil (.childCons currentInnerCons .childNil))))
                                    .childNil))) :=
                          Step.cong .gen_app ()
                            (StepChildren.here
                              (.childCons
                                (.mkGen .gen_listElim ()
                                  (.childCons tail
                                    (.childCons currentInnerNil (.childCons currentInnerCons .childNil))))
                                .childNil : RawTermChildren [0] scope)
                              (Step.cong .gen_app ()
                                (StepChildren.here
                                  (.childCons tail .childNil : RawTermChildren [0] scope)
                                  (Step.cong .gen_app ()
                                    (StepChildren.here
                                      (.childCons head .childNil : RawTermChildren [0] scope) consStep)))))
                        have hopTwo :
                            Step
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app ()
                                    (.childCons
                                      (.mkGen .gen_app () (.childCons consAfter (.childCons head .childNil)))
                                      (.childCons tail .childNil)))
                                  (.childCons
                                    (.mkGen .gen_listElim ()
                                      (.childCons tail
                                        (.childCons currentInnerNil (.childCons currentInnerCons .childNil))))
                                    .childNil)))
                              (listElimConsContractum consAfter head tail currentInnerNil) :=
                          Step.cong .gen_app ()
                            (StepChildren.there (headShift := 0)
                              (.mkGen .gen_app ()
                                (.childCons
                                  (.mkGen .gen_app () (.childCons consAfter (.childCons head .childNil)))
                                  (.childCons tail .childNil)))
                              (StepChildren.here .childNil
                                (Step.cong .gen_listElim ()
                                  (StepChildren.there (headShift := 0) tail
                                    (StepChildren.there (headShift := 0) currentInnerNil
                                      (StepChildren.here .childNil consStep))))))
                        exact (((currentInnerConsContractum head tail headTerminates tailTerminates).inv
                          hopOne).inv hopTwo))
                currentConsTerminates currentInnerNilContractum)
          currentNilTerminates currentConsTerminates currentConsContractum))
    scrutineeTerminates)
    nilBranchTerminates consBranchTerminates consContractumTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.StepStar.listElim_isStronglyNormalizing_of_strongly_normalizing_branches_probe
