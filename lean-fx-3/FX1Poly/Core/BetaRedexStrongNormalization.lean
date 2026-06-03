import FX1Poly.Core.ApplicationStrongNormalizationForward
import FX1Poly.Core.ReducibleTypeForwardClosure

/-! # FX1Poly/Core/BetaRedexStrongNormalization
    — the single-contractum β-redex SN lemma (neutral arm of the member weak-head β-expansion)

The general β-redex `app (lam body) arg` is strongly normalizing once the binder `lam body`, the argument
`arg`, and the SINGLE β-contractum `subst0 body arg` are SN — the body is free to step.  This is the
ergonomic shape a reducibility / fundamental-theorem lambda arm needs: that arm establishes membership of the
contractum `subst0 body arg` in a codomain candidate (hence its SN, the neutral candidate being `IsStronglyNormalizing`),
and needs the redex `app (lam body) arg` to inherit SN.  It is the neutral arm of the denote-layer member
weak-head β-expansion (the lambda-arm engine toward SN-043 / #672).

Two existing siblings in `StrongNormalizationRedexes` are NOT this lemma:
  * `appLam_isStronglyNormalizing_of_normal_body_contractum` fixes a NORMAL (non-stepping) body;
  * `appLam_isStronglyNormalizing_of_body_argument_contractum` requires a UNIFORM contractum-SN
    (`∀ body' arg', SN body' → SN arg' → SN (subst0 body' arg')`) over ALL body/argument reducts.
This lemma needs only the single contractum at the given `body`/`arg`; the body-reduct contractums are
recovered by `descendStepStar` along `StepStar.subst0Body` (a body chain `body ↝* body'` descends
`subst0 body arg ↝* subst0 body' arg`), and argument reduction is absorbed by the application-SN core lemma
`isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing`.

The supporting `stepStarLamInversion` is reusable substrate: a `StepStar` chain out of a lambda lands on a
lambda, and the body chain is recovered.

## Zero-axiom verification

`stepStarLamInversion` is induction on the chain with `Step.from_lam` maintaining the lam shape; the redex
lemma instantiates the application-SN core lemma and discharges its β-contraction obligation via the
inversion + `StepStar.subst0Body` + `descendStepStar`.  No `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation
open StepStar

/-- **lam-StepStar inversion (full form).**  A `StepStar` chain out of a lambda lands on a lambda, and the
body chain is recovered.  Induction on the chain; `Step.from_lam` maintains the lambda shape at each step. -/
theorem stepStarLamInversion {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ body : RawTerm (scope + 1),
      source = .mkGen .gen_lam () (.childCons body .childNil) →
      ∃ bodyFinal : RawTerm (scope + 1),
        target = .mkGen .gen_lam () (.childCons bodyFinal .childNil) ∧
          StepStar body bodyFinal := by
  induction chain with
  | refl term =>
      intro body sourceEquation
      exact ⟨body, sourceEquation, StepStar.refl body⟩
  | trans headStep _restChain restInductiveHypothesis =>
      intro body sourceEquation
      subst sourceEquation
      obtain ⟨bodyAfter, secondEquation, bodyStep⟩ := Step.from_lam headStep
      obtain ⟨bodyFinal, targetEquation, bodyRest⟩ := restInductiveHypothesis bodyAfter secondEquation
      exact ⟨bodyFinal, targetEquation, StepStar.trans bodyStep bodyRest⟩

/-- **lam-StepStar body chain.**  Specialization of `stepStarLamInversion` when the target is already known to
be a lambda: a chain `lam body ↝* lam bodyFinal` yields the body chain `body ↝* bodyFinal`.  The `mkGen`/`childCons`
injection drills through the dependent index equations to reach the body-head equation. -/
theorem stepStarLamBodyChain {scope : Nat} {body bodyFinal : RawTerm (scope + 1)}
    (chain : StepStar (.mkGen .gen_lam () (.childCons body .childNil))
                      (.mkGen .gen_lam () (.childCons bodyFinal .childNil))) :
    StepStar body bodyFinal := by
  obtain ⟨bodyFinalRecovered, lamEquation, bodyChain⟩ := stepStarLamInversion chain body rfl
  injection lamEquation with _scopeEquation _generatorEquation _payloadEquation childrenEquation
  injection childrenEquation with _childScopeEquation _childShiftEquation _childRestShiftsEquation
    bodyEquation _childTailEquation
  rw [bodyEquation]; exact bodyChain

/-- **Single-contractum β-redex SN.**  `app (lam body) arg` is strongly normalizing given the binder
`lam body`, the argument `arg`, and the single β-contractum `subst0 body arg` are SN — the body is free to
step.  Discharges the β-contraction obligation of
`isStronglyNormalizing_applicationCell_ofBetaContractionsStronglyNormalizing`: for any body reduct `body'`
(`lam body ↝* lam body'`, by `stepStarLamBodyChain`), the contractum `subst0 body' arg` is SN because
`subst0 body arg ↝* subst0 body' arg` (`StepStar.subst0Body`) descends from `contractumStronglyNormalizing`. -/
theorem appLam_isStronglyNormalizing_of_contractum {scope : Nat}
    {body : RawTerm (scope + 1)} {arg : RawTerm scope}
    (lamStronglyNormalizing :
      IsStronglyNormalizing (.mkGen .gen_lam () (.childCons body .childNil)))
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
