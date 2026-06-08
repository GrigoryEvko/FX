import FX1Poly.Core.StepInversion
import FX1Poly.Core.StepSubst
import FX1Poly.Core.StrongNormalizationApplication

namespace FX1Poly.Core

open StepStar

-- Forward SN closure along a StepStar chain (Acc.inv iterated).
theorem sn_forward_probe {scope : Nat} {term reduct : RawTerm scope}
    (termSN : IsStronglyNormalizing term) (chain : StepStar term reduct) :
    IsStronglyNormalizing reduct := by
  induction chain with
  | refl => exact termSN
  | trans headStep _rest restIH => exact restIH (termSN.inv headStep)

-- SN of application: the load-bearing lemma for member weak-head-expansion / recursor reducibility.
-- Auxiliary with `∀ arg` in the statement so inducting on fnSN cleanly generalizes the argument.
theorem app_isStronglyNormalizing_aux_probe {scope : Nat} {fn : RawTerm scope}
    (fnSN : IsStronglyNormalizing fn) :
    ∀ arg : RawTerm scope, IsStronglyNormalizing arg →
      (∀ body : RawTerm (scope + 1),
        StepStar fn (.mkGen .gen_lam () (.childCons body .childNil)) →
        IsStronglyNormalizing (RawTerm.subst0 body arg)) →
      IsStronglyNormalizing
        (.mkGen .gen_app () (.childCons fn (.childCons arg .childNil))) := by
  induction fnSN with
  | intro functionWitness _functionAccessors functionIH =>
      intro arg argSN
      induction argSN with
      | intro argumentWitness _argumentAccessors argumentIH =>
          intro betaContractionsSN
          apply Acc.intro
          intro reduct stepToReduct
          rcases Step.from_app stepToReduct with
            ⟨body, functionIsLam, reductIsContractum⟩ |
            ⟨functionAfter, reductIsFunctionStep, functionStep⟩ |
            ⟨argumentAfter, reductIsArgumentStep, argumentStep⟩
          · subst reductIsContractum
            subst functionIsLam
            exact betaContractionsSN body (StepStar.refl _)
          · subst reductIsFunctionStep
            exact functionIH functionAfter functionStep argumentWitness
              (Acc.intro argumentWitness _argumentAccessors)
              (fun body chain => betaContractionsSN body (StepStar.trans functionStep chain))
          · subst reductIsArgumentStep
            refine argumentIH argumentAfter argumentStep (fun body chain => ?_)
            exact sn_forward_probe (betaContractionsSN body chain)
              (Step.subst0Argument body argumentStep)

theorem app_isStronglyNormalizing_probe {scope : Nat} {fn arg : RawTerm scope}
    (fnSN : IsStronglyNormalizing fn) (argSN : IsStronglyNormalizing arg)
    (betaContractionsSN : ∀ body : RawTerm (scope + 1),
        StepStar fn (.mkGen .gen_lam () (.childCons body .childNil)) →
        IsStronglyNormalizing (RawTerm.subst0 body arg)) :
    IsStronglyNormalizing
      (.mkGen .gen_app () (.childCons fn (.childCons arg .childNil))) :=
  app_isStronglyNormalizing_aux_probe fnSN arg argSN betaContractionsSN

end FX1Poly.Core

#print axioms FX1Poly.Core.sn_forward_probe
#print axioms FX1Poly.Core.app_isStronglyNormalizing_probe
