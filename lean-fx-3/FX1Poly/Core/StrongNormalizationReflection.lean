import FX1Poly.Core.StepSubst
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Core/StrongNormalizationReflection
    — strong normalization is REFLECTED by `subst0` instantiation

`subst0` instantiation preserves reduction in the body: a body step `Step body body'` lifts to a step
`Step (subst0 body arg) (subst0 body' arg)` (`Step.subst` at the singleton substitution).  Hence if the
INSTANTIATED term `subst0 body arg` is strongly normalizing, so is the body — any infinite body reduction
would lift to an infinite reduction of the instantiation.  This is the anti-substitution (reflection)
direction of SN, the converse of the (false-in-general) preservation direction.

The fundamental theorem's `genFormationPi` arm uses it to discharge the open-codomain
strong-normalization obligation WITHOUT a binder-lifted reducible environment: the codomain interpreted at
a (variable) argument is a reducible type — hence strongly normalizing — and `subst0` reflects that SN back
to the open codomain.  So the dependent Π-former membership rule's `codomainNormalizing` premise follows
from its `codomainExists` premise; no renaming-stability of the reducibility relation is required.

## Zero-axiom verification

Well-founded `Acc` induction over the instantiation's strong-normalization accessibility, generalized by an
equation to free the accessible index (the standard reflect-accessibility pattern); each body step is
transported to an instantiation step by `Step.subst`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation
open StepStar

/-- **`subst0` reflects strong normalization.**  If the instantiation `subst0 body argument` is strongly
normalizing then so is `body`.  Proof: `body`'s strong-normalization accessibility is reconstructed from the
instantiation's by well-founded recursion — every step `Step body bodyReduct` lifts (via `Step.subst` at the
singleton) to `Step (subst0 body argument) (subst0 bodyReduct argument)`, a strictly smaller node in the
instantiation's accessibility tree, so the inductive hypothesis hands back the reduct's accessibility. -/
theorem IsStronglyNormalizing.ofSubst0Body {scope : Nat}
    {body : RawTerm (scope + 1)} {argument : RawTerm scope}
    (instantiationNormalizing : IsStronglyNormalizing (RawTerm.subst0 body argument)) :
    IsStronglyNormalizing body := by
  have reflectAccessibility :
      ∀ {instantiation : RawTerm scope}, Acc StepSuccessor instantiation →
        ∀ candidate : RawTerm (scope + 1),
          instantiation = RawTerm.subst0 candidate argument →
          Acc StepSuccessor candidate := by
    intro instantiation accessible
    induction accessible with
    | intro _current _accessibleCurrent inductiveHypothesis =>
        intro candidate currentEquation
        refine Acc.intro candidate (fun candidateReduct candidateStep => ?_)
        have instantiationStep :
            Step (RawTerm.subst0 candidate argument)
              (RawTerm.subst0 candidateReduct argument) :=
          Step.subst (RawTermSubst.singleton argument) candidateStep
        exact inductiveHypothesis (RawTerm.subst0 candidateReduct argument)
          (currentEquation ▸ instantiationStep) candidateReduct rfl
  exact reflectAccessibility instantiationNormalizing body rfl

end FX1Poly.Core
