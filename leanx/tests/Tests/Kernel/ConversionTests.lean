import FX.Kernel.Conversion

/-!
# Conversion tests

Compile-time tests for `convEq` — definitional equality up to
beta-reduction, iota-reduction, delta-reduction (on transparent
consts), and Pi-eta, per `fx_design.md` §31 and Appendix H.9.

Design principle: every positive (convEq = true) test is paired
with a nearby negative test varying exactly one field.  A broken
`convEq = fun _ _ _ => true` or `convEq = fun _ _ _ => false`
both fail somewhere.

Coverage: every kernel constructor
(var, const, app, lam, pi, sigma, type, forallLevel, ind, ctor,
indRec, coind, id, refl, idJ, quot, quotMk, quotLift) has at
least one positive and one negative test.  Grade differences,
level differences, name differences, index differences, and
list-length differences are all tested.
-/

namespace Tests.Kernel.ConversionTests

open FX.Kernel
open FX.Kernel.Term

def universeZero : Level := .zero
def universeOne : Level := .succ .zero
def universeTwo : Level := .succ universeOne
def typeZero : Term := .type universeZero
def typeOne : Term := .type universeOne
def typeTwo : Term := .type universeTwo
def v0 : Term := .var 0
def v1 : Term := .var 1
def v2 : Term := .var 2

/-! ## var-equivalence — de Bruijn makes this syntactic equality -/

example : convEq 10 (Term.var 0) (Term.var 0) = true := by native_decide
example : convEq 10 (Term.var 5) (Term.var 5) = true := by native_decide
example : convEq 10 (Term.var 0) (Term.var 1) = false := by native_decide
example : convEq 10 (Term.var 5) (Term.var 6) = false := by native_decide
example : convEq 10 (Term.var 99) (Term.var 100) = false := by native_decide

/-! ## type-equivalence — via Level.equiv -/

example : convEq 10 typeZero typeZero = true := by native_decide
example : convEq 10 typeOne typeOne = true := by native_decide
example : convEq 10 typeTwo typeTwo = true := by native_decide

example : convEq 10 typeZero typeOne = false := by native_decide
example : convEq 10 typeOne typeZero = false := by native_decide
example : convEq 10 typeOne typeTwo = false := by native_decide

-- Level.equiv uses `eval?` — `max zero zero` evaluates to zero.
-- This tests the non-syntactic level equivalence.
example :
  convEq 10 (.type (.max .zero .zero)) typeZero = true := by native_decide
example :
  convEq 10 typeOne (.type (.max (.succ .zero) .zero)) = true := by
  native_decide
example :
  convEq 10 (.type (.max (.succ .zero) (.succ (.succ .zero)))) typeTwo
    = true := by native_decide

/-! ## beta-equivalence — the whnf reduction fires -/

-- (λ x. x) T₀ ≡ T₀
example :
  convEq 10
    (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero)
    typeZero
  = true := by native_decide

-- (λ x. x) T₀ ≡ T₁  is FALSE (redex reduces to T₀, T₀ ≠ T₁).
example :
  convEq 10
    (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeZero)
    typeOne
  = false := by native_decide

-- (λ x. x) T₁ ≡ T₁  — check with a different level so a broken
-- reduction that returned a fixed term would fail.
example :
  convEq 10
    (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeOne)
    typeOne
  = true := by native_decide

-- (λ _. body) arg  reduces to body when body doesn't mention var 0.
-- Here body = type 0 (no free vars), so (λ x. Type₀) anything → Type₀.
example :
  convEq 10
    (Term.app (Term.lam Grade.default typeZero typeZero) typeOne)
    typeZero
  = true := by native_decide

-- Redex on both sides, reducing to the same thing.
example :
  convEq 10
    (Term.app (Term.lam Grade.default typeZero v0) typeZero)
    (Term.app (Term.lam Grade.default typeZero v0) typeZero)
  = true := by native_decide

-- Two different redexes reducing to DIFFERENT values.
example :
  convEq 10
    (Term.app (Term.lam Grade.default typeZero v0) typeZero)
    (Term.app (Term.lam Grade.default typeZero v0) typeOne)
  = false := by native_decide

/-! ## Structural: lam — every field matters -/

-- Positive baseline.
example :
  convEq 10
    (Term.lam Grade.default typeZero (Term.var 0))
    (Term.lam Grade.default typeZero (Term.var 0))
  = true := by native_decide

-- Differing grade → not equal.
example :
  convEq 10
    (Term.lam Grade.default typeZero (Term.var 0))
    (Term.lam Grade.ghost typeZero (Term.var 0))
  = false := by native_decide

-- Differing domain type → not equal.  (Old tests missed this —
-- both sides used the same `typeZero` domain.)
example :
  convEq 10
    (Term.lam Grade.default typeZero (Term.var 0))
    (Term.lam Grade.default typeOne (Term.var 0))
  = false := by native_decide

-- Differing body → not equal.
example :
  convEq 10
    (Term.lam Grade.default typeZero (Term.var 0))
    (Term.lam Grade.default typeZero (Term.var 1))
  = false := by native_decide

/-! ## Structural: pi — every field matters -/

example :
  convEq 10
    (Term.piTot Grade.default typeZero typeZero)
    (Term.piTot Grade.default typeZero typeZero)
  = true := by native_decide

-- Differing grade on pi.
example :
  convEq 10
    (Term.piTot Grade.default typeZero typeZero)
    (Term.piTot Grade.ghost typeZero typeZero)
  = false := by native_decide

-- Differing domain.
example :
  convEq 10
    (Term.piTot Grade.default typeZero typeZero)
    (Term.piTot Grade.default typeOne typeZero)
  = false := by native_decide

-- Differing codomain.
example :
  convEq 10
    (Term.piTot Grade.default typeZero typeZero)
    (Term.piTot Grade.default typeZero typeOne)
  = false := by native_decide

/-! ## Structural: sigma — every field matters -/

example :
  convEq 10
    (Term.sigma Grade.default typeZero typeZero)
    (Term.sigma Grade.default typeZero typeZero)
  = true := by native_decide

example :
  convEq 10
    (Term.sigma Grade.default typeZero typeZero)
    (Term.sigma Grade.ghost typeZero typeZero)
  = false := by native_decide

example :
  convEq 10
    (Term.sigma Grade.default typeZero typeZero)
    (Term.sigma Grade.default typeOne typeZero)
  = false := by native_decide

example :
  convEq 10
    (Term.sigma Grade.default typeZero typeZero)
    (Term.sigma Grade.default typeZero typeOne)
  = false := by native_decide

/-! ## Structural: forallLevel -/

example : convEq 10 (.forallLevel typeZero) (.forallLevel typeZero)
    = true := by native_decide

example : convEq 10 (.forallLevel typeZero) (.forallLevel typeOne)
    = false := by native_decide

-- forallLevel of non-type bodies.
example : convEq 10 (.forallLevel v0) (.forallLevel v0) = true := by
  native_decide

example : convEq 10 (.forallLevel v0) (.forallLevel v1) = false := by
  native_decide

-- forallLevel vs non-forallLevel.
example : convEq 10 (.forallLevel v0) v0 = false := by native_decide

/-! ## Structural: const -/

-- Two identical const names are equal (opaque-by-name).
example : convEq 10 (.const "foo") (.const "foo") = true := by native_decide

-- Two different const names are NOT equal.
example : convEq 10 (.const "foo") (.const "bar") = false := by native_decide
example : convEq 10 (.const "double") (.const "triple") = false := by
  native_decide

-- const vs other constructor.
example : convEq 10 (.const "foo") v0 = false := by native_decide
example : convEq 10 (.const "foo") typeZero = false := by native_decide

/-! ## Structural: ind -/

-- Same name + same args.
example :
  convEq 10 (.ind "List" [typeZero]) (.ind "List" [typeZero]) = true := by
  native_decide

-- Empty-args variant.
example :
  convEq 10 (.ind "Bool" []) (.ind "Bool" []) = true := by native_decide

-- Different names → not equal even with equal args.
example :
  convEq 10 (.ind "List" [typeZero]) (.ind "Vec" [typeZero]) = false := by
  native_decide

-- Same name, different args.
example :
  convEq 10 (.ind "List" [typeZero]) (.ind "List" [typeOne]) = false := by
  native_decide

-- Different arity (empty vs one).
example :
  convEq 10 (.ind "Box" []) (.ind "Box" [typeZero]) = false := by
  native_decide

/-! ## Structural: ctor -/

-- Baseline equality.
example :
  convEq 10
    (.ctor "Nat" 0 [] [])
    (.ctor "Nat" 0 [] [])
  = true := by native_decide

-- Different name.
example :
  convEq 10
    (.ctor "Nat" 0 [] [])
    (.ctor "Int" 0 [] [])
  = false := by native_decide

-- Different ctor index.
example :
  convEq 10
    (.ctor "Nat" 0 [] [])
    (.ctor "Nat" 1 [] [])
  = false := by native_decide

-- Different type-args.
example :
  convEq 10
    (.ctor "Pair" 0 [typeZero] [])
    (.ctor "Pair" 0 [typeOne] [])
  = false := by native_decide

-- Different value-args.
example :
  convEq 10
    (.ctor "Succ" 1 [] [(.ctor "Nat" 0 [] [])])
    (.ctor "Succ" 1 [] [(.ctor "Nat" 0 [] [(.ctor "Nat" 0 [] [])])])
  = false := by native_decide

-- Non-trivial positive: Succ Zero ≡ Succ Zero.
example :
  convEq 10
    (.ctor "Nat" 1 [] [(.ctor "Nat" 0 [] [])])
    (.ctor "Nat" 1 [] [(.ctor "Nat" 0 [] [])])
  = true := by native_decide

/-! ## Structural: indRec -/

-- Baseline equal.
example :
  convEq 10
    (.indRec "Nat" typeZero [v0] v1)
    (.indRec "Nat" typeZero [v0] v1)
  = true := by native_decide

-- Different spec name.
example :
  convEq 10
    (.indRec "Nat" typeZero [v0] v1)
    (.indRec "Int" typeZero [v0] v1)
  = false := by native_decide

-- Different motive.
example :
  convEq 10
    (.indRec "Nat" typeZero [v0] v1)
    (.indRec "Nat" typeOne [v0] v1)
  = false := by native_decide

-- Different methods (arity differs).
example :
  convEq 10
    (.indRec "Nat" typeZero [v0] v1)
    (.indRec "Nat" typeZero [v0, v1] v1)
  = false := by native_decide

-- Different target.
example :
  convEq 10
    (.indRec "Nat" typeZero [v0] v1)
    (.indRec "Nat" typeZero [v0] v2)
  = false := by native_decide

/-! ## Structural: coind — name + args comparison (post-A2) -/

-- Same name + same args: equal.
example : convEq 10 (.coind "stream" []) (.coind "stream" [] : Term) = true :=
  by native_decide
example : convEq 10
    (.coind "stream" [typeZero])
    (.coind "stream" [typeZero] : Term) = true :=
  by native_decide

-- Different names: not equal.
example : convEq 10 (.coind "stream" []) (.coind "other" [] : Term) = false :=
  by native_decide

-- Same name, different args: not equal.
example : convEq 10
    (.coind "stream" [typeZero])
    (.coind "stream" [typeOne] : Term) = false :=
  by native_decide

-- coind vs non-coind.
example : convEq 10 (.coind "stream" []) typeZero = false := by native_decide

/-! ## Structural: id — every field matters -/

-- Baseline.
example :
  convEq 10
    (Term.id typeZero (Term.var 0) (Term.var 0))
    (Term.id typeZero (Term.var 0) (Term.var 0))
  = true := by native_decide

-- Differing base type.
example :
  convEq 10
    (Term.id typeZero v0 v0)
    (Term.id typeOne v0 v0)
  = false := by native_decide

-- Differing lhs.
example :
  convEq 10
    (Term.id typeZero v0 v1)
    (Term.id typeZero v1 v1)
  = false := by native_decide

-- Differing rhs.
example :
  convEq 10
    (Term.id typeZero v0 v0)
    (Term.id typeZero v0 v1)
  = false := by native_decide

/-! ## Structural: refl -/

example : convEq 10 (.refl v0) (.refl v0) = true := by native_decide
example : convEq 10 (.refl typeZero) (.refl typeZero) = true := by
  native_decide

-- Differing witness.
example : convEq 10 (.refl v0) (.refl v1) = false := by native_decide
example : convEq 10 (.refl typeZero) (.refl typeOne) = false := by
  native_decide

-- refl vs non-refl.
example : convEq 10 (.refl v0) v0 = false := by native_decide

/-! ## Structural: idJ -/

-- Baseline: non-refl eqProof so whnf leaves the idJ stuck and
-- convEq compares structurally (not after iota-reduction).
example :
  convEq 10
    (.idJ typeZero v0 v1)
    (.idJ typeZero v0 v1)
  = true := by native_decide

-- Differing motive — use non-refl eqProof to prevent iota firing
-- (iota drops the motive, so on `.refl _` the motive diff would
-- be invisible to convEq).
example :
  convEq 10
    (.idJ typeZero v0 v1)
    (.idJ typeOne v0 v1)
  = false := by native_decide

-- Differing base.
example :
  convEq 10
    (.idJ typeZero v0 v2)
    (.idJ typeZero v1 v2)
  = false := by native_decide

-- Differing eqProof.
example :
  convEq 10
    (.idJ typeZero v0 v1)
    (.idJ typeZero v0 v2)
  = false := by native_decide

-- IdJ iota reduction: `idJ _ base (refl witness)` → `app base witness`.
-- LHS has a refl eqProof, so whnf reduces it.
example :
  convEq 10
    (.idJ typeZero v0 (.refl typeZero))
    (Term.app v0 typeZero)
  = true := by native_decide

-- If RHS doesn't match the reduct, convEq rejects.
example :
  convEq 10
    (.idJ typeZero v0 (.refl typeZero))
    (Term.app v0 typeOne)
  = false := by native_decide

/-! ## Structural: quot -/

example :
  convEq 10
    (Term.quot typeZero (Term.var 0))
    (Term.quot typeZero (Term.var 0))
  = true := by native_decide

-- Differing carrier type.
example :
  convEq 10
    (Term.quot typeZero v0)
    (Term.quot typeOne v0)
  = false := by native_decide

-- Differing relation.
example :
  convEq 10
    (Term.quot typeZero v0)
    (Term.quot typeZero v1)
  = false := by native_decide

/-! ## Structural: quotMk -/

example :
  convEq 10
    (.quotMk v0 v1)
    (.quotMk v0 v1)
  = true := by native_decide

-- Differing relation.
example :
  convEq 10
    (.quotMk v0 v1)
    (.quotMk v2 v1)
  = false := by native_decide

-- Differing witness.
example :
  convEq 10
    (.quotMk v0 v1)
    (.quotMk v0 v2)
  = false := by native_decide

/-! ## Structural: quotLift -/

example :
  convEq 10
    (.quotLift v0 v1 v2)
    (.quotLift v0 v1 v2)
  = true := by native_decide

-- Differing lifted.
example :
  convEq 10
    (.quotLift v0 v1 v2)
    (.quotLift (Term.var 3) v1 v2)
  = false := by native_decide

-- Differing respects-proof.
example :
  convEq 10
    (.quotLift v0 v1 v2)
    (.quotLift v0 (Term.var 3) v2)
  = false := by native_decide

-- Differing target.
example :
  convEq 10
    (.quotLift v0 v1 v2)
    (.quotLift v0 v1 (Term.var 3))
  = false := by native_decide

-- QuotLift iota reduction: `quotLift f _ (quotMk _ w)` → `app f w`.
example :
  convEq 10
    (.quotLift typeZero v0 (.quotMk v1 typeOne))
    (Term.app typeZero typeOne)
  = true := by native_decide

-- RHS doesn't match the reduct.
example :
  convEq 10
    (.quotLift typeZero v0 (.quotMk v1 typeOne))
    (Term.app typeZero typeZero)
  = false := by native_decide

/-! ## Cross-constructor negatives -/

example : convEq 10 v0 typeZero = false := by native_decide
example :
  convEq 10 (Term.app v0 v1) v0 = false := by native_decide
example :
  convEq 10 typeZero (Term.lam Grade.default typeZero typeZero) = false := by
  native_decide
example :
  convEq 10 (.refl v0) (.quotMk v0 v0) = false := by native_decide
example :
  convEq 10 (.ind "List" []) (.ctor "List" 0 [] []) = false := by
  native_decide
example :
  convEq 10 (Term.piTot Grade.default typeZero typeZero)
             (Term.sigma Grade.default typeZero typeZero)
    = false := by native_decide

/-! ## Level.equiv — equal evaluations equate -/

example : Level.equiv Level.zero Level.zero = true := by native_decide
example : Level.equiv (Level.max .zero .zero) .zero = true := by native_decide
example : Level.equiv Level.zero (Level.succ .zero) = false := by native_decide
example : Level.equiv (Level.succ .zero) (Level.succ .zero) = true := by
  native_decide
example :
  Level.equiv (Level.max (.succ .zero) .zero) (.succ .zero)
    = true := by native_decide
example :
  Level.equiv (Level.max .zero (.succ (.succ .zero))) (.succ (.succ .zero))
    = true := by native_decide

/-! ## Pi-η — `λ _. f (var 0)` ≡ `f` when `f` doesn't mention var 0

This is NEW coverage — the old test file had zero η tests despite
Pi-η being a core Appendix H.9 convertibility rule.  A regression
that disabled the η arm in `convEq` would go unnoticed. -/

-- η-reduction: λ_. (var 1) (var 0) ≡ var 0 (after binder pop).
-- Here the lambda body is `app f (var 0)` with `f = var 1`
-- (references outer); f does not mention var 0.
example :
  convEq 10
    (Term.lam Grade.default typeZero
      (Term.app (Term.var 1) (Term.var 0)))
    (Term.var 0)
  = true := by native_decide

-- Symmetric: non-lambda on left, lambda-η-redex on right.
example :
  convEq 10
    (Term.var 0)
    (Term.lam Grade.default typeZero
      (Term.app (Term.var 1) (Term.var 0)))
  = true := by native_decide

-- η fails when f mentions the bound var — `f (var 0)` with f
-- containing var 0 would be `var 0 (var 0)`, and we bind it
-- inside the lambda, so there's no η-collapse.
example :
  convEq 10
    (Term.lam Grade.default typeZero
      (Term.app (Term.var 0) (Term.var 0)))
    (Term.var 0)
  = false := by native_decide

-- η fails when the body isn't `app _ (var 0)`.
example :
  convEq 10
    (Term.lam Grade.default typeZero (Term.var 0))
    (Term.var 0)
  = false := by native_decide

/-! ## `conv` — default-fuel entry wrapping `convEq` -/

example : conv typeZero typeZero = true := by native_decide
example : conv typeZero typeOne = false := by native_decide
example : conv v0 v0 = true := by native_decide
example : conv v0 v1 = false := by native_decide

-- Redex reduces with default fuel.
example :
  conv (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeOne) typeOne
    = true := by native_decide

-- Negative default-fuel case.
example :
  conv (Term.app (Term.lam Grade.default typeZero (Term.var 0)) typeOne) typeZero
    = false := by native_decide

/-! ## Fuel behavior — 0 fuel returns false (conservative) -/

-- The fuel-0 guard at the top of convEq returns false before any
-- structural match.  Even for `x = x`, fuel 0 ⇒ false.
example : convEq 0 typeZero typeZero = false := by native_decide
example : convEq 0 v0 v0 = false := by native_decide

-- Fuel 1 suffices for simple leaf comparisons.
example : convEq 1 typeZero typeZero = true := by native_decide
example : convEq 1 v0 v0 = true := by native_decide
example : convEq 1 (.const "x") (.const "x") = true := by native_decide

end Tests.Kernel.ConversionTests
