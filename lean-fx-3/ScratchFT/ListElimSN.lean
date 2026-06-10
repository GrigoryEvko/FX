import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationIotaRedexes

namespace FX1Poly.Core
namespace StepStar

-- head subterm-SN (mirror firstComponent_of_pair, gen_listCons)
theorem headValue_isStronglyNormalizing_of_listCons_probe {scope : Nat}
    {headValue tailValue : RawTerm scope}
    (consTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_listCons () (.childCons headValue (.childCons tailValue .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing headValue := by
  suffices general :
      ∀ {consTerm : RawTerm scope}, Acc StepSuccessor consTerm →
        ∀ {currentHead currentTail : RawTerm scope},
          consTerm = .mkGen .gen_listCons ()
            (.childCons currentHead (.childCons currentTail .childNil)) →
          Acc StepSuccessor currentHead from
    general consTerminates rfl
  intro consTerm consAccessible
  induction consAccessible with
  | intro consWitness _consPredecessors consInductiveHypothesis =>
      intro currentHead currentTail witnessEq
      subst witnessEq
      apply Acc.intro
      intro headAfter headStep
      have congruenceLift :
          Step
            (.mkGen .gen_listCons ()
              (.childCons currentHead (.childCons currentTail .childNil)) : RawTerm scope)
            (.mkGen .gen_listCons ()
              (.childCons headAfter (.childCons currentTail .childNil)) : RawTerm scope) :=
        Step.cong .gen_listCons ()
          (StepChildren.here
            (.childCons currentTail .childNil : RawTermChildren [0] scope) headStep)
      exact consInductiveHypothesis
        (.mkGen .gen_listCons () (.childCons headAfter (.childCons currentTail .childNil)))
        congruenceLift rfl

-- tail subterm-SN (mirror secondComponent_of_pair, gen_listCons)
theorem tailValue_isStronglyNormalizing_of_listCons_probe {scope : Nat}
    {headValue tailValue : RawTerm scope}
    (consTerminates :
      IsStronglyNormalizing
        (.mkGen .gen_listCons () (.childCons headValue (.childCons tailValue .childNil)) :
          RawTerm scope)) :
    IsStronglyNormalizing tailValue := by
  suffices general :
      ∀ {consTerm : RawTerm scope}, Acc StepSuccessor consTerm →
        ∀ {currentHead currentTail : RawTerm scope},
          consTerm = .mkGen .gen_listCons ()
            (.childCons currentHead (.childCons currentTail .childNil)) →
          Acc StepSuccessor currentTail from
    general consTerminates rfl
  intro consTerm consAccessible
  induction consAccessible with
  | intro consWitness _consPredecessors consInductiveHypothesis =>
      intro currentHead currentTail witnessEq
      subst witnessEq
      apply Acc.intro
      intro tailAfter tailStep
      have congruenceLift :
          Step
            (.mkGen .gen_listCons ()
              (.childCons currentHead (.childCons currentTail .childNil)) : RawTerm scope)
            (.mkGen .gen_listCons ()
              (.childCons currentHead (.childCons tailAfter .childNil)) : RawTerm scope) :=
        Step.cong .gen_listCons ()
          (@StepChildren.there scope 0 [0] currentHead _ _
            (StepChildren.here (.childNil : RawTermChildren [] scope) tailStep))
      exact consInductiveHypothesis
        (.mkGen .gen_listCons () (.childCons currentHead (.childCons tailAfter .childNil)))
        congruenceLift rfl

-- conditional listElim-cons iota-redex SN (normal motive + branches + cons-contractum hypothesis)
-- Phase-Z motive shape: motive first (under one binder), scrutinee last; a single Acc.ndrec over the
-- scrutinee with the motive and both branches held fixed-normal by hypothesis.
theorem listElim_isStronglyNormalizing_of_normal_branches_probe {scope : Nat}
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveHasNoStep : ∀ targetMotive : RawTerm (scope + 1), Step motive targetMotive → False)
    (nilBranchHasNoStep : ∀ targetNil : RawTerm scope, Step nilBranch targetNil → False)
    (consBranchHasNoStep : ∀ targetCons : RawTerm scope, Step consBranch targetCons → False)
    (consContractumTerminates :
      ∀ {headValue tailValue : RawTerm scope},
        IsStronglyNormalizing headValue → IsStronglyNormalizing tailValue →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app ()
                    (.childCons consBranch (.childCons headValue .childNil)))
                  (.childCons tailValue .childNil)))
              (.childCons
                (.mkGen .gen_listElim ()
                  (.childCons motive
                    (.childCons nilBranch
                      (.childCons consBranch (.childCons tailValue .childNil)))))
                .childNil)) : RawTerm scope))
    (scrutineeTerminates : IsStronglyNormalizing scrutinee) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons motive
          (.childCons nilBranch
            (.childCons consBranch (.childCons scrutinee .childNil)))) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentScrutinee =>
      IsStronglyNormalizing
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope))
    (m := fun currentScrutinee currentScrutineeSuccessors scrutineeIH =>
      Acc.intro
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons currentScrutinee .childNil)))) :
          RawTerm scope)
        (fun targetTerm listElimStep => by
          rcases Step.from_listElim listElimStep with
            ⟨_scrutineeIsNil, targetIsNil⟩ |
            ⟨headValue, tailValue, scrutineeIsCons, targetIsContractum⟩ |
            ⟨motiveAfter, _targetIsMotiveStep, motiveStep⟩ |
            ⟨nilAfter, _targetIsNilStep, nilStep⟩ |
            ⟨consAfter, _targetIsConsStep, consStep⟩ |
            ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
          · rw [targetIsNil]
            exact isStronglyNormalizing_of_noStep nilBranchHasNoStep
          · rw [targetIsContractum]
            have currentScrutineeSN : IsStronglyNormalizing currentScrutinee :=
              Acc.intro currentScrutinee currentScrutineeSuccessors
            rw [scrutineeIsCons] at currentScrutineeSN
            exact consContractumTerminates
              (headValue_isStronglyNormalizing_of_listCons_probe currentScrutineeSN)
              (tailValue_isStronglyNormalizing_of_listCons_probe currentScrutineeSN)
          · exact absurd motiveStep (motiveHasNoStep motiveAfter)
          · exact absurd nilStep (nilBranchHasNoStep nilAfter)
          · exact absurd consStep (consBranchHasNoStep consAfter)
          · rw [targetIsScrutineeStep]
            exact scrutineeIH scrutineeAfter scrutineeStep))
    scrutineeTerminates

end StepStar
end FX1Poly.Core

#print axioms FX1Poly.Core.StepStar.headValue_isStronglyNormalizing_of_listCons_probe
#print axioms FX1Poly.Core.StepStar.tailValue_isStronglyNormalizing_of_listCons_probe
#print axioms FX1Poly.Core.StepStar.listElim_isStronglyNormalizing_of_normal_branches_probe
