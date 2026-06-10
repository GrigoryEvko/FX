import FX1Poly.Core.StrongNormalizationListElim

namespace FX1Poly.Core
open FX1Poly.Foundation
namespace StepStar

/-- The listElim cons-contractum
`app (app (app consBranch head) tail) (listElim motive nilBranch consBranch tail)`.  Phase-Z motive shape:
the recursive `listElim` THREADS the motive (under one binder) and carries the tail as its LAST child. -/
private abbrev listElimConsContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (consBranch head tail nilBranch : RawTerm scope) :
    RawTerm scope :=
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

theorem listElim_isStronglyNormalizing_of_strongly_normalizing_branches_probe {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {scrutinee nilBranch consBranch : RawTerm scope}
    (consContractumTerminates :
      ∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractum motive consBranch head tail nilBranch))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee)
    (motiveTerminates : IsStronglyNormalizing motive)
    (nilBranchTerminates : IsStronglyNormalizing nilBranch)
    (consBranchTerminates : IsStronglyNormalizing consBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons motive
          (.childCons nilBranch
            (.childCons consBranch (.childCons scrutinee .childNil))))) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      ∀ {currentMotive : RawTerm (scope + 1)} {currentNil currentCons : RawTerm scope},
        IsStronglyNormalizing currentMotive →
        IsStronglyNormalizing currentNil → IsStronglyNormalizing currentCons →
          (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
            IsStronglyNormalizing
              (listElimConsContractum currentMotive currentCons head tail currentNil)) →
          IsStronglyNormalizing
            (.mkGen .gen_listElim ()
              (.childCons currentMotive
                (.childCons currentNil
                  (.childCons currentCons (.childCons currentScrutinee .childNil))))))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH => by
      intro currentMotive currentNil currentCons
        currentMotiveTerminates currentNilTerminates currentConsTerminates currentConsContractum
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerMotive =>
            ∀ {currentNil currentCons : RawTerm scope},
              IsStronglyNormalizing currentNil → IsStronglyNormalizing currentCons →
                (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
                  IsStronglyNormalizing (listElimConsContractum innerMotive currentCons head tail currentNil)) →
                IsStronglyNormalizing
                  (.mkGen .gen_listElim ()
                    (.childCons innerMotive
                      (.childCons currentNil
                        (.childCons currentCons (.childCons currentScrutinee .childNil))))))
          (m := fun currentInnerMotive currentInnerMotiveSuccessors motiveIH => by
            intro currentNil currentCons currentNilTerminates currentConsTerminates currentInnerMotiveContractum
            exact
              (Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerNil =>
                  ∀ {currentCons : RawTerm scope},
                    IsStronglyNormalizing currentCons →
                      (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
                        IsStronglyNormalizing
                          (listElimConsContractum currentInnerMotive currentCons head tail innerNil)) →
                        IsStronglyNormalizing
                          (.mkGen .gen_listElim ()
                            (.childCons currentInnerMotive
                              (.childCons innerNil
                                (.childCons currentCons (.childCons currentScrutinee .childNil))))))
                (m := fun currentInnerNil currentInnerNilSuccessors nilIH => by
                  intro currentCons currentConsTerminates currentInnerNilContractum
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerCons =>
                        (∀ head tail : RawTerm scope, IsStronglyNormalizing head → IsStronglyNormalizing tail →
                          IsStronglyNormalizing
                            (listElimConsContractum currentInnerMotive innerCons head tail currentInnerNil)) →
                          IsStronglyNormalizing
                            (.mkGen .gen_listElim ()
                              (.childCons currentInnerMotive
                                (.childCons currentInnerNil
                                  (.childCons innerCons (.childCons currentScrutinee .childNil))))))
                      (m := fun currentInnerCons currentInnerConsSuccessors consIH => by
                            intro currentInnerConsContractum
                            apply Acc.intro
                            intro targetTerm listElimStep
                            rcases Step.from_listElim listElimStep with
                              ⟨_scrutineeIsNil, targetIsNil⟩ |
                              ⟨headValue, tailValue, scrutineeIsCons, targetIsContractum⟩ |
                              ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                              ⟨nilAfter, targetIsNilStep, nilStep⟩ |
                              ⟨consAfter, targetIsConsStep, consStep⟩ |
                              ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                            · rw [targetIsNil]
                              exact Acc.intro currentInnerNil currentInnerNilSuccessors
                            · rw [targetIsContractum]
                              have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
                                Acc.intro currentScrutinee currentScrutineeSuccessors
                              rw [scrutineeIsCons] at currentScrutineeSN
                              exact currentInnerConsContractum headValue tailValue
                                (headValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
                                (tailValue_isStronglyNormalizing_of_listCons currentScrutineeSN)
                            · rw [targetIsMotiveStep]
                              refine motiveIH motiveAfter motiveStep
                                (Acc.intro currentInnerNil currentInnerNilSuccessors)
                                (Acc.intro currentInnerCons currentInnerConsSuccessors)
                                (fun head tail headTerminates tailTerminates => ?_)
                              exact (currentInnerConsContractum head tail headTerminates tailTerminates).inv
                                (Step.cong .gen_app ()
                                  (StepChildren.there (headShift := 0)
                                    (.mkGen .gen_app ()
                                      (.childCons
                                        (.mkGen .gen_app ()
                                          (.childCons currentInnerCons (.childCons head .childNil)))
                                        (.childCons tail .childNil)))
                                    (StepChildren.here .childNil
                                      (Step.cong .gen_listElim ()
                                        (StepChildren.here
                                          (.childCons currentInnerNil
                                            (.childCons currentInnerCons
                                              (.childCons tail .childNil)) :
                                            RawTermChildren [0, 0, 0] scope)
                                          motiveStep)))))
                            · rw [targetIsNilStep]
                              refine nilIH nilAfter nilStep
                                (Acc.intro currentInnerCons currentInnerConsSuccessors)
                                (fun head tail headTerminates tailTerminates => ?_)
                              exact (currentInnerConsContractum head tail headTerminates tailTerminates).inv
                                (Step.cong .gen_app ()
                                  (StepChildren.there (headShift := 0)
                                    (.mkGen .gen_app ()
                                      (.childCons
                                        (.mkGen .gen_app ()
                                          (.childCons currentInnerCons (.childCons head .childNil)))
                                        (.childCons tail .childNil)))
                                    (StepChildren.here .childNil
                                      (Step.cong .gen_listElim ()
                                        (StepChildren.there (headShift := 1) currentInnerMotive
                                          (StepChildren.here
                                            (.childCons currentInnerCons
                                              (.childCons tail .childNil) :
                                              RawTermChildren [0, 0] scope)
                                            nilStep))))))
                            · rw [targetIsConsStep]
                              refine consIH consAfter consStep (fun head tail headTerminates tailTerminates => ?_)
                              have hopOne :
                                  Step (listElimConsContractum currentInnerMotive currentInnerCons head tail
                                          currentInnerNil)
                                    (.mkGen .gen_app ()
                                      (.childCons
                                        (.mkGen .gen_app ()
                                          (.childCons
                                            (.mkGen .gen_app ()
                                              (.childCons consAfter (.childCons head .childNil)))
                                            (.childCons tail .childNil)))
                                        (.childCons
                                          (.mkGen .gen_listElim ()
                                            (.childCons currentInnerMotive
                                              (.childCons currentInnerNil
                                                (.childCons currentInnerCons (.childCons tail .childNil)))))
                                          .childNil))) :=
                                Step.cong .gen_app ()
                                  (StepChildren.here
                                    (.childCons
                                      (.mkGen .gen_listElim ()
                                        (.childCons currentInnerMotive
                                          (.childCons currentInnerNil
                                            (.childCons currentInnerCons (.childCons tail .childNil)))))
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
                                            (.mkGen .gen_app ()
                                              (.childCons consAfter (.childCons head .childNil)))
                                            (.childCons tail .childNil)))
                                        (.childCons
                                          (.mkGen .gen_listElim ()
                                            (.childCons currentInnerMotive
                                              (.childCons currentInnerNil
                                                (.childCons currentInnerCons (.childCons tail .childNil)))))
                                          .childNil)))
                                    (listElimConsContractum currentInnerMotive consAfter head tail
                                      currentInnerNil) :=
                                Step.cong .gen_app ()
                                  (StepChildren.there (headShift := 0)
                                    (.mkGen .gen_app ()
                                      (.childCons
                                        (.mkGen .gen_app ()
                                          (.childCons consAfter (.childCons head .childNil)))
                                        (.childCons tail .childNil)))
                                    (StepChildren.here .childNil
                                      (Step.cong .gen_listElim ()
                                        (StepChildren.there (headShift := 1) currentInnerMotive
                                          (StepChildren.there (headShift := 0) currentInnerNil
                                            (StepChildren.here
                                              (.childCons tail .childNil : RawTermChildren [0] scope)
                                              consStep))))))
                              exact (((currentInnerConsContractum head tail headTerminates tailTerminates).inv
                                hopOne).inv hopTwo)
                            · rw [targetIsScrutineeStep]
                              exact scrutineeIH scrutineeAfter scrutineeStep
                                (Acc.intro currentInnerMotive currentInnerMotiveSuccessors)
                                (Acc.intro currentInnerNil currentInnerNilSuccessors)
                                (Acc.intro currentInnerCons currentInnerConsSuccessors)
                                currentInnerConsContractum)
                      currentConsTerminates currentInnerNilContractum)
                currentNilTerminates currentConsTerminates currentInnerMotiveContractum)
          currentMotiveTerminates currentNilTerminates currentConsTerminates currentConsContractum))
    scrutineeTerminates)
    motiveTerminates nilBranchTerminates consBranchTerminates consContractumTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.StepStar.listElim_isStronglyNormalizing_of_strongly_normalizing_branches_probe
