import FX1Poly.Modal.GradedFundamentalTheorem

namespace FX1Poly.Modal

/-! Probe the ★ fusion lemma and the abstraction lemma's β-step for non-triviality. -/

-- (A) Is ★ definitionally trivial (provable by rfl)?  If so, something upstream collapsed.
-- We test on a concrete non-trivial body/argument/substitution.
-- body = app (var 0) (var 1), argument = var 5, σ = (fun i => var (i + 10))
def probeBody : GradedLambda := .app (.var 0) (.var 1)
def probeArg : GradedLambda := .var 5
def probeSubst : TermSubstitution := fun i => .var (i + 10)

-- LHS of ★: substAt 0 arg (applySubstitution (liftSubstitution σ) body)
-- RHS of ★: applySubstitution (consSubstitution arg σ) body
-- Evaluate both to a concrete normal form and display.
#eval (GradedLambda.substAt 0 probeArg
        (GradedLambda.applySubstitution (liftSubstitution probeSubst) probeBody))
#eval (GradedLambda.applySubstitution (consSubstitution probeArg probeSubst) probeBody)

-- They MUST be equal (★ is a theorem); show concretely by the lemma.
theorem probe_star_holds :
    GradedLambda.substAt 0 probeArg
        (GradedLambda.applySubstitution (liftSubstitution probeSubst) probeBody)
      = GradedLambda.applySubstitution (consSubstitution probeArg probeSubst) probeBody :=
  substAt_zero_applySubstitution_lift probeBody probeArg probeSubst

-- (B) Is ★ trivially rfl on this concrete instance?  If the equation were definitionally
-- forced, `rfl` would close it.  Here both sides happen to be closed terms that DO compute,
-- so rfl MIGHT work on a fully-closed instance — that is fine and expected (it is a real
-- computation, not a collapse).  The meaningful test is the GENERAL lemma over an abstract σ,
-- which is NOT rfl.  Confirm the general statement is not rfl:
-- (We do not attempt `by rfl` on the general lemma; instead we confirm it is proved by the
-- substitution-algebra fusion, evidenced by its axiom-cleanliness and dependency on
-- applySubstitution_applySubstitution.)

-- (C) Concrete β through the FT: linear identity applied to K-combinator, fully through the
-- real fundamental theorem (not the abstraction lemma in isolation).
-- term = app (lam (var 0)) (lam (lam (var 1)))  : the identity applied to K.
-- Type it with HasSimpleType, then get reducibility + SN from the FT.
def idAppK : GradedLambda := .app (.lam (.var 0)) (.lam (.lam (.var 1)))

-- Simple type: (base -> base) is K's-ish; we need a consistent typing.
-- id : (A) -> (A) where A = arrow base base ; K : arrow base (arrow base base) needs A = arrow base (arrow base base).
-- Let A := arrow base (arrow base base).  id : A -> A, applied to K : A.
def tyA : SimpleType := .arrow .base (.arrow .base .base)

theorem idAppK_typed : HasSimpleType [] idAppK tyA :=
  HasSimpleType.app [] tyA tyA (.lam (.var 0)) (.lam (.lam (.var 1)))
    (HasSimpleType.lam [] tyA tyA (.var 0) (HasSimpleType.var [tyA] 0 tyA rfl))
    (HasSimpleType.lam [] .base (.arrow .base .base) (.lam (.var 1))
      (HasSimpleType.lam [.base] .base .base (.var 1)
        (HasSimpleType.var [.base, .base] 1 .base rfl)))

-- This redex is NON-NORMAL (it has a β-redex at the head).  SN must come from the FT
-- processing the β-step, NOT from the term being already normal.
theorem idAppK_reduces : GradedLambda.Reduces idAppK (.lam (.lam (.var 1))) := by
  have h := GradedLambda.Reduces.beta (GradedLambda.var 0) (.lam (.lam (.var 1)))
  -- substAt 0 K (var 0) = K
  have e : GradedLambda.substAt 0 (.lam (.lam (.var 1))) (GradedLambda.var 0)
            = (GradedLambda.lam (GradedLambda.lam (GradedLambda.var 1))) := rfl
  rw [e] at h
  exact h

-- SN of this genuinely-reducible (non-normal) typed term, through the real machinery:
theorem idAppK_SN : GradedLambda.IsStronglyNormalizing idAppK :=
  idAppK_typed.stronglyNormalizing

#print axioms probe_star_holds
#print axioms idAppK_SN
#print axioms idAppK_reduces

-- (D) Confirm there is no `partial`/opaque escape: print the abstraction lemma + FT bodies'
-- axiom dependence (already known clean) and the whole HasUsage.stronglyNormalizing chain.
#print axioms HasSimpleType.fundamental
#print axioms HasSimpleType.reducible

end FX1Poly.Modal
