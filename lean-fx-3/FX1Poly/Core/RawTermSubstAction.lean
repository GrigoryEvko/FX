import FX1Poly.Core.RawTermSubstCompose
import FX1Poly.Core.RawTermSubstIdentity

/-! # Foundation/PolyCell/Core/RawTermSubstAction — Action typeclass instance

The full `FX1Poly.Foundation.Action RawTermSubst` typeclass instance,
citing the three Action laws:

  * `apply_ext` — covered by `RawTerm.subst_pointwise`
  * `identity_apply` — covered by `RawTerm.subst_identity_apply`
  * `compose_assoc` — covered by `RawTerm.subst_compose`

Plus the supporting infrastructure it builds on:

  * `RawTermSubst.identity`
  * `RawTermSubst.compose`
  * `RawTermSubst.lift`
  * `subst_identity_apply`
  * `subst_compose`

`RawTermSubst.compose` semantically requires `RawTerm.subst`
(`compose s1 s2 pos = subst s2 (s1 pos)`), and `RawTerm.subst` is
defined via fold over `LiftsRaw` (the minimal typeclass fold needs —
just `liftForRaw`), so `RawTermSubst` carries `LiftsRaw` before the
full Action instance closes.

## The instance shape

Each typeclass field maps directly to the substitution infrastructure:

  ActionTarget := RawTerm                     -- substituents are terms
  headIndex sigma pos := sigma pos              -- direct lookup
  liftForTy / liftForRaw sigma := sigma.lift    -- same lift for both binder kinds
  identity := RawTermSubst.identity
  compose := RawTermSubst.compose
  composeAtHeadIndex s1 s2 pos := subst s2 (s1 pos)  -- = (compose s1 s2) pos

The four laws:
  compose_assoc_pointwise   : cite subst_compose
  compose_identity_left     : rfl (fold var-arm reduction)
  compose_identity_right    : cite subst_identity_apply
  headIndex_compose         : rfl (compose's defn matches composeAtHeadIndex)

## Why same `lift` for liftForTy and liftForRaw

The `Action` typeclass exposes TWO lift methods (per
`Foundation/Action.lean` R11) to accommodate ctors that bind a Ty
under a binder (piTy/sigmaTy) vs ctors that bind a RawTerm under a
binder (refine/lam/pathLam).  For concrete instances where the
two lifts coincide (Subst, SubstHet, Renaming, and RawTermSubst),
both methods point to the same `RawTermSubst.lift`.

## Zero-axiom verification

All declarations propext-free:
* The instance itself — definitional unfolding + cite the three
  laws.
* The four equivalence theorems below (`identity_eq_action`,
  `lift_eq_actionForTy`, `lift_eq_actionForRaw`, `compose_eq_action`)
  — definitional `rfl`.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — The Action typeclass instance

The polynomial monad's structure made explicit at the typeclass
layer.  After this instance is in scope, `RawTermSubst` becomes
a fully-functioning Allais-style Action container, suitable for
abstract recursion engines and law-driven proofs. -/

/-- `Action` instance for `RawTermSubst`.

Substitutions form a polynomial-monad-style Action over RawTerm:
they compose, have an identity, lift under binders, and satisfy
the three monoid laws (associativity and two-sided identity).

* `ActionTarget` is `RawTerm`: variables map to terms.
* `headIndex sigma pos` is just `sigma pos`.
* `liftForTy` and `liftForRaw` coincide as `RawTermSubst.lift`
  for this instance (the binder shape is the same at the raw
  layer; the dual-lift exists in the typeclass for instances
  where the two MUST diverge).
* `identity` and `compose` are the canonical operations.
* `composeAtHeadIndex` exposes the composed action's effect at a
  single position opaquely; for us it equals
  `subst secondSigma (firstSigma position)` by direct definition.

The four laws:
* `compose_assoc_pointwise`: cite `subst_compose`.
  Reduces to `subst s3 (subst s2 (s1 pos)) = subst (compose s2 s3) (s1 pos)`,
  which IS subst_compose applied to `s1 pos`.
* `compose_identity_left_pointwise`: `rfl`.  After unfolding,
  becomes `subst sigma (identity pos) = sigma pos`.  The identity
  substitution at pos is `mkGen .gen_var pos .childNil`; fold's
  var arm reduces `subst sigma (mkGen .gen_var pos .childNil)`
  to `sigma pos`.
* `compose_identity_right_pointwise`: cite `subst_identity_apply`.
  Reduces to `subst identity (sigma pos) = sigma pos`,
  which IS subst_identity_apply applied to `sigma pos`.
* `headIndex_compose`: `rfl`.  Both sides reduce to
  `subst secondSigma (firstSigma pos)` by compose's definition.
-/
instance instActionRawTermSubst : FX1Poly.Foundation.Action RawTermSubst where
  ActionTarget       := RawTerm
  headIndex          := fun someSubstitution position =>
    someSubstitution position
  liftForTy          := fun someSubstitution => someSubstitution.lift
  liftForRaw         := fun someSubstitution => someSubstitution.lift
  identity           := RawTermSubst.identity
  compose            := RawTermSubst.compose
  composeAtHeadIndex := fun firstSubstitution secondSubstitution position =>
    RawTerm.subst secondSubstitution (firstSubstitution position)
  compose_assoc_pointwise firstSubstitution middleSubstitution
      lastSubstitution position := by
    -- Goal (after unfolding composeAtHeadIndex on both sides):
    --   subst lastSigma (subst middleSigma (firstSigma pos))
    --   = subst (compose middleSigma lastSigma) (firstSigma pos)
    -- Which is exactly RawTerm.subst_compose applied at
    -- term = firstSigma pos.
    exact RawTerm.subst_compose middleSubstitution lastSubstitution
            (firstSubstitution position)
  compose_identity_left_pointwise someSubstitution position := by
    -- Goal (after unfolding composeAtHeadIndex):
    --   subst someSubstitution (identity position) = someSubstitution position
    -- identity position = mkGen .gen_var position .childNil; fold's
    -- var arm reduces this to `someSubstitution position`.  Closes
    -- by rfl.
    rfl
  compose_identity_right_pointwise someSubstitution position := by
    -- Goal (after unfolding composeAtHeadIndex):
    --   subst identity (someSubstitution position) = someSubstitution position
    -- Which is RawTerm.subst_identity_apply applied at
    -- term = someSubstitution position.
    exact RawTerm.subst_identity_apply (someSubstitution position)
  headIndex_compose firstSubstitution secondSubstitution position := by
    -- Goal:
    --   (compose firstSigma secondSigma) position
    --   = composeAtHeadIndex firstSigma secondSigma position
    -- By compose's defn: `(compose firstSigma secondSigma) position =
    --   subst secondSigma (firstSigma position)`.
    -- By composeAtHeadIndex's defn: same expression.  rfl.
    rfl

/-! ## Section 2 — Equivalence theorems

Witness that the manually-named operations agree with the
Action-typeclass-derived operations.  Useful for proofs that
straddle the manual / typeclass API. -/

/-- `RawTermSubst.identity` is the Action instance's identity. -/
theorem RawTermSubst.identity_eq_action {scope : Nat} :
    (RawTermSubst.identity : RawTermSubst scope scope) =
      (FX1Poly.Foundation.Action.identity : RawTermSubst scope scope) := rfl

/-- `RawTermSubst.lift` agrees with the Action instance's
`liftForTy`. -/
theorem RawTermSubst.lift_eq_actionForTy
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope) :
    someSubstitution.lift = FX1Poly.Foundation.Action.liftForTy someSubstitution := rfl

/-- `RawTermSubst.lift` agrees with the Action instance's
`liftForRaw`. -/
theorem RawTermSubst.lift_eq_actionForRaw
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope) :
    someSubstitution.lift = FX1Poly.Foundation.Action.liftForRaw someSubstitution := rfl

/-- `RawTermSubst.compose` is the Action instance's `compose`. -/
theorem RawTermSubst.compose_eq_action
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubst sourceScope middleScope)
    (secondSubstitution : RawTermSubst middleScope targetScope) :
    RawTermSubst.compose firstSubstitution secondSubstitution =
      FX1Poly.Foundation.Action.compose firstSubstitution secondSubstitution := rfl

/-! ## Section 3 — Smoke tests

Verify the instance and the equivalence theorems invoke cleanly. -/

/-- Smoke: the Action instance's `headIndex` of identity at any
position returns `mkGen .gen_var pos .childNil`. -/
theorem RawTermSubst.action_identity_headIndex_smoke {scope : Nat}
    (position : Fin scope) :
    FX1Poly.Foundation.Action.headIndex
        (FX1Poly.Foundation.Action.identity : RawTermSubst scope scope) position =
      (.mkGen .gen_var position .childNil : RawTerm scope) := rfl

/-- Smoke: the Action instance's `compose_identity_left` law fires
on a concrete substitution + position 0 of a lifted scope. -/
theorem RawTermSubst.action_compose_identity_left_smoke
    {scope : Nat}
    (someSubstitution : RawTermSubst (scope + 1) (scope + 1)) :
    FX1Poly.Foundation.Action.composeAtHeadIndex
        (FX1Poly.Foundation.Action.identity : RawTermSubst (scope + 1) (scope + 1))
        someSubstitution
        (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1)) =
      FX1Poly.Foundation.Action.headIndex someSubstitution
        (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1)) := by
  exact FX1Poly.Foundation.Action.compose_identity_left_pointwise someSubstitution _

end FX1Poly.Core
