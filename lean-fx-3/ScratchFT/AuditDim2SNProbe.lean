import FX1Poly.Modal.GradedFundamentalTheorem

namespace FX1Poly.Modal

/-! Adversarial audit probes for DIM2 SN. -/

-- (1) Exact definition of IsStronglyNormalizing: must be Acc over reversed Reduces edge.
#print GradedLambda.IsStronglyNormalizing

-- (2) Exact definition of Reducible: base must be IsStronglyNormalizing (NOT True).
#print GradedLambda.Reducible

-- (3) Exact Reduces relation.
#print GradedLambda.Reducible.sn
#print GradedLambda.IsNeutral

-- (4) The looping omega combinator Omega = (λx. x x)(λx. x x).
def selfApp : GradedLambda := .lam (.app (.var 0) (.var 0))
def omega : GradedLambda := .app selfApp selfApp

-- Omega β-reduces to itself.  This proves Reduces is NON-EMPTY and self-looping.
theorem omega_steps_to_itself : GradedLambda.Reduces omega omega := by
  have h : GradedLambda.Reduces omega (GradedLambda.substAt 0 selfApp (.app (.var 0) (.var 0))) :=
    GradedLambda.Reduces.beta (.app (.var 0) (.var 0)) selfApp
  -- compute the substitution result
  have e : GradedLambda.substAt 0 selfApp (.app (.var 0) (.var 0)) = omega := by rfl
  rw [e] at h
  exact h

-- (5) THE GOLD-STANDARD NON-VACUITY TEST:
-- Omega is NOT strongly normalizing.  If IsStronglyNormalizing were `True` or trivially
-- inhabited, this would be UNPROVABLE (you cannot refute True).  That it IS provable means
-- IsStronglyNormalizing genuinely rules out infinite reduction.
theorem omega_not_SN : ¬ GradedLambda.IsStronglyNormalizing omega := by
  intro sn
  -- Acc.rec: from accessibility, every element reachable is accessible; Omega reaches itself,
  -- so we get an infinite descent.  Standard: Acc of a self-looping point is impossible.
  have notAcc : ∀ (t : GradedLambda), t = omega → ¬ GradedLambda.IsStronglyNormalizing t := by
    intro t teq snt
    induction snt with
    | intro x _ ih =>
        subst teq
        exact ih omega omega_steps_to_itself rfl
  exact notAcc omega rfl sn

-- (6) If IsStronglyNormalizing were trivial, this `sorry`-free contradiction proof would be
-- impossible.  Combined: SN of a typed term is real, SN of Omega is refuted.
-- Sanity: linear identity IS SN through the real machinery.
example : GradedLambda.IsStronglyNormalizing (GradedLambda.lam (GradedLambda.var 0)) :=
  linearIdentity_stronglyNormalizing

-- (7) Can the looping term even be typed?  It MUST NOT be HasSimpleType-typable (self-app needs
-- infinite type).  We do not try to prove untypability here, only that SN machinery does not
-- secretly accept Omega.

-- (8) Axiom audit on the headline + the abstraction lemma + the star lemma.
#print axioms HasUsage.stronglyNormalizing
#print axioms HasSimpleType.stronglyNormalizing
#print axioms GradedLambda.Reducible.abstraction
#print axioms substAt_zero_applySubstitution_lift
#print axioms GradedLambda.reducibilityConditions
#print axioms omega_not_SN

end FX1Poly.Modal
