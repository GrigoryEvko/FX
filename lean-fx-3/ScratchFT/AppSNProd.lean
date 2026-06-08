import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst
import FX1Poly.Core.StrongNormalizationApplication

namespace FX1Poly.Core

open StepStar

-- Forward SN closure along a StepStar chain (Acc.inv iterated) — production name.
theorem IsStronglyNormalizing.descendStepStar {scope : Nat} {sourceTerm reductTerm : RawTerm scope}
    (sourceStronglyNormalizing : IsStronglyNormalizing sourceTerm)
    (chain : StepStar sourceTerm reductTerm) :
    IsStronglyNormalizing reductTerm := by
  induction chain with
  | refl => exact sourceStronglyNormalizing
  | trans headStep _rest restIH => exact restIH (sourceStronglyNormalizing.inv headStep)

-- SN of application under the beta-contraction side-condition — auxiliary with `∀ arg` in the
-- statement so inducting on the function's SN cleanly generalizes the argument.
theorem isStronglyNormalizing_applicationCell_aux {scope : Nat} {functionTerm : RawTerm scope}
    (functionStronglyNormalizing : IsStronglyNormalizing functionTerm) :
    ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      (∀ body : RawTerm (scope + 1),
        StepStar functionTerm (.mkGen .gen_lam () (.childCons body .childNil)) →
        IsStronglyNormalizing (RawTerm.subst0 body argument)) →
      IsStronglyNormalizing (applicationCell functionTerm argument) := by
  induction functionStronglyNormalizing with
  | intro functionWitness _functionAccessors functionIH =>
      intro argument argumentStronglyNormalizing
      induction argumentStronglyNormalizing with
      | intro argumentWitness _argumentAccessors argumentIH =>
          intro betaContractionsStronglyNormalizing
          apply Acc.intro
          intro reduct stepToReduct
          rcases Step.from_app stepToReduct with
            ⟨body, functionIsLam, reductIsContractum⟩ |
            ⟨functionAfter, reductIsFunctionStep, functionStep⟩ |
            ⟨argumentAfter, reductIsArgumentStep, argumentStep⟩
          · subst reductIsContractum
            subst functionIsLam
            exact betaContractionsStronglyNormalizing body (StepStar.refl _)
          · subst reductIsFunctionStep
            exact functionIH functionAfter functionStep argumentWitness
              (Acc.intro argumentWitness _argumentAccessors)
              (fun body chain =>
                betaContractionsStronglyNormalizing body (StepStar.trans functionStep chain))
          · subst reductIsArgumentStep
            refine argumentIH argumentAfter argumentStep (fun body chain => ?_)
            exact IsStronglyNormalizing.descendStepStar
              (betaContractionsStronglyNormalizing body chain)
              (Step.subst0Argument body argumentStep)

/-- **SN of an application under the beta-contraction side-condition.**  `app functionTerm argument` is
strongly normalizing when the function and argument are SN AND every β-contraction of the function (once it
weak-head-reduces to a `lam`) against the argument is SN.  The side-condition is essential — SN of the two
positions alone does NOT give SN of the application (the Ω term `app (lam (app v0 v0)) (lam (app v0 v0))`). -/
theorem isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing
    {scope : Nat} {functionTerm argument : RawTerm scope}
    (functionStronglyNormalizing : IsStronglyNormalizing functionTerm)
    (argumentStronglyNormalizing : IsStronglyNormalizing argument)
    (betaContractionsStronglyNormalizing : ∀ body : RawTerm (scope + 1),
        StepStar functionTerm (.mkGen .gen_lam () (.childCons body .childNil)) →
        IsStronglyNormalizing (RawTerm.subst0 body argument)) :
    IsStronglyNormalizing (applicationCell functionTerm argument) :=
  isStronglyNormalizing_applicationCell_aux functionStronglyNormalizing argument
    argumentStronglyNormalizing betaContractionsStronglyNormalizing

end FX1Poly.Core

#print axioms FX1Poly.Core.IsStronglyNormalizing.descendStepStar
#print axioms FX1Poly.Core.isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing
