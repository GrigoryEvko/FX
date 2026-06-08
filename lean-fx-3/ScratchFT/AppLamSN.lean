import FX1Poly.Core.ApplicationStrongNormalizationForward
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.ReducibleTypeForwardClosure

/-! Scratch: the GENERAL β-redex SN lemma (neutral arm of the member weak-head β-expansion / lambda-arm
engine): `app (lam body) arg` is SN when `lam body`, `arg`, and the contractum `subst0 body arg` are SN.
The body is allowed to STEP (unlike the existing `appLam_isStronglyNormalizing_of_normal_body_contractum`,
which fixes a normal body). Discharges the `betaContractions` obligation of
`isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing` via a lam-StepStar inversion. -/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **lam-StepStar inversion (full form).** A StepStar chain out of a lambda lands on a lambda, and the
body chain is recovered. Induction on the chain; `Step.from_lam` maintains the lam shape per step. -/
theorem stepStarLamInversion {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ body : RawTerm (scope + 1),
      source = .mkGen .gen_lam () (.childCons body .childNil) →
      ∃ bodyFinal : RawTerm (scope + 1),
        target = .mkGen .gen_lam () (.childCons bodyFinal .childNil) ∧
          StepStar body bodyFinal := by
  induction chain with
  | refl term =>
      intro body sourceEq
      exact ⟨body, sourceEq, StepStar.refl body⟩
  | trans headStep _restChain restInductiveHypothesis =>
      intro body sourceEq
      subst sourceEq
      obtain ⟨bodyAfter, secondEq, bodyStep⟩ := Step.from_lam headStep
      obtain ⟨bodyFinal, targetEq, bodyRest⟩ := restInductiveHypothesis bodyAfter secondEq
      exact ⟨bodyFinal, targetEq, StepStar.trans bodyStep bodyRest⟩

/-- **lam-StepStar body chain.** Specializes the inversion when the target is already known to be a lambda. -/
theorem stepStarLamBodyChain {scope : Nat} {body bodyFinal : RawTerm (scope + 1)}
    (chain : StepStar (.mkGen .gen_lam () (.childCons body .childNil))
                      (.mkGen .gen_lam () (.childCons bodyFinal .childNil))) :
    StepStar body bodyFinal := by
  obtain ⟨bodyFinalRecovered, lamEquation, bodyChain⟩ := stepStarLamInversion chain body rfl
  injection lamEquation with _scopeEquation _generatorEquation _payloadEquation childrenEquation
  injection childrenEquation with _childScopeEquation _childShiftEquation _childRestShiftsEquation
    bodyEquation _childTailEquation
  rw [bodyEquation]; exact bodyChain

/-- **General β-redex SN.** `app (lam body) arg` is SN given the binder, argument, and contractum are SN
(body free to step). The neutral arm of the member weak-head β-expansion. -/
theorem appLam_isStronglyNormalizing {scope : Nat} {body : RawTerm (scope + 1)} {arg : RawTerm scope}
    (lamStronglyNormalizing : IsStronglyNormalizing (.mkGen .gen_lam () (.childCons body .childNil)))
    (argumentStronglyNormalizing : IsStronglyNormalizing arg)
    (contractumStronglyNormalizing : IsStronglyNormalizing (RawTerm.subst0 body arg)) :
    IsStronglyNormalizing
      (applicationCell (.mkGen .gen_lam () (.childCons body .childNil)) arg) := by
  refine isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing
    lamStronglyNormalizing argumentStronglyNormalizing ?_
  intro bodyFinal chain
  exact IsStronglyNormalizing.descendStepStar contractumStronglyNormalizing
    (StepStar.subst0Body arg (stepStarLamBodyChain chain))

end FX1Poly.Core

#print axioms FX1Poly.Core.stepStarLamInversion
#print axioms FX1Poly.Core.appLam_isStronglyNormalizing
