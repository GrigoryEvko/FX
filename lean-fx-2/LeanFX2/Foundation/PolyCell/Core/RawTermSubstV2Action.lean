import LeanFX2.Foundation.PolyCell.Core.RawTermV2SubstCompose
import LeanFX2.Foundation.PolyCell.Core.RawTermV2SubstIdentity

/-! # Foundation/PolyCell/Core/RawTermSubstV2Action — Action typeclass instance

THE FINISH LINE OF V2-L2.7.

This file ships the full `LeanFX2.Action RawTermSubstV2` typeclass
instance, citing the three Action laws that landed across the
previous commits in this layer:

  * `apply_ext` — covered by `RawTermV2.subst_pointwise`        (#181a)
  * `identity_apply` — covered by `RawTermV2.subst_identity_apply` (#181b)
  * `compose_assoc` — covered by `RawTermV2.subst_compose`       (#181c6)

Plus the supporting infrastructure shipped along the way:

  * `RawTermSubstV2.identity`              (#175)
  * `RawTermSubstV2.compose`               (#181c6)
  * `RawTermSubstV2.lift`                  (#180)
  * `subst_identity_apply`                 (#181b)
  * `subst_compose`                        (#181c6)

## Closes the chicken-and-egg from #180

At #180 (subst via foldV2), the full `Action RawTermSubstV2`
instance couldn't ship because:
* `RawTermSubstV2.compose` semantically requires `RawTermV2.subst`
  (compose s1 s2 pos = subst s2 (s1 pos)).
* `RawTermV2.subst` was being DEFINED via foldV2.
* foldV2 originally required `[Action Container]` — circular.

The #180 refactor introduced `LiftsRaw` as the minimal typeclass
foldV2 actually needs (just `liftForRaw`).  The chicken-and-egg
was resolved: `RawTermSubstV2` got `LiftsRaw` immediately, `subst`
got defined, and now — finally — the FULL Action instance ships.

## Position in the V2-L2.7 ladder

  V2-L2.7a apply_ext      (#181a, shipped) ──┐
  V2-L2.7b identity_apply (#181b, shipped) ──┤── three Action laws ✓
  V2-L2.7c compose_assoc  (#181c6 shipped)  ──┘
  rename_pointwise        (#181c1, shipped)
  rename lift_compose     (#181c2, shipped)
  rename_compose          (#181c3, shipped)
  rename_subst_commute    (#181c4, shipped)
  subst_rename_commute    (#181c5, shipped)
  subst_compose           (#181c6, shipped)
  Action instance         (THIS COMMIT — closes V2-L2.7)

After this commit, V2-L2.7 is COMPLETE and #181 closes entirely.

## The instance shape

Each typeclass field maps directly to v2 infrastructure:

  ActionTarget := RawTermV2                     -- substituents are terms
  headIndex sigma pos := sigma pos              -- direct lookup
  liftForTy / liftForRaw sigma := sigma.lift    -- same lift for both binder kinds
  identity := RawTermSubstV2.identity           -- shipped #175
  compose := RawTermSubstV2.compose             -- shipped #181c6
  composeAtHeadIndex s1 s2 pos := subst s2 (s1 pos)  -- = (compose s1 s2) pos

The four laws:
  compose_assoc_pointwise   : cite subst_compose         (#181c6)
  compose_identity_left     : rfl (foldV2 var-arm reduction)
  compose_identity_right    : cite subst_identity_apply  (#181b)
  headIndex_compose         : rfl (compose's defn matches composeAtHeadIndex)

## Why same `lift` for liftForTy and liftForRaw

The `Action` typeclass exposes TWO lift methods (per
`Foundation/Action.lean` R11) to accommodate ctors that bind a Ty
under a binder (piTy/sigmaTy) vs ctors that bind a RawTerm under a
binder (refine/lam/pathLam).  For concrete instances where the
two lifts coincide (Subst, SubstHet, Renaming, and our
RawTermSubstV2), both methods point to the same `RawTermSubstV2.lift`.

## Zero-axiom verification

All declarations propext-free:
* The instance itself — definitional unfolding + cite the three
  shipped laws.
* The four equivalence theorems below (`identity_eq_action`,
  `lift_eq_actionForTy`, `lift_eq_actionForRaw`, `compose_eq_action`)
  — definitional `rfl`.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.

## v1 comparison

v1 ships an analogous `Action RawTermSubst` instance at
`Foundation/RawSubst/ActionInstances.lean` lines 86-116.  Same
shape, same proofs.  The difference is purely the underlying
substrate (v1's RawTerm vs v2's RawTermV2) and the v2 argument
order on `subst` and `rename` (substitution/renaming first, term
second — flipped from v1).
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-! ## Section 1 — The Action typeclass instance

The polynomial monad's structure made explicit at the typeclass
layer.  After this instance is in scope, `RawTermSubstV2` becomes
a fully-functioning Allais-style Action container, suitable for
abstract recursion engines and law-driven proofs. -/

/-- `Action` instance for `RawTermSubstV2`.

Substitutions form a polynomial-monad-style Action over RawTermV2:
they compose, have an identity, lift under binders, and satisfy
the three monoid laws (associativity and two-sided identity).

* `ActionTarget` is `RawTermV2`: variables map to terms.
* `headIndex sigma pos` is just `sigma pos`.
* `liftForTy` and `liftForRaw` coincide as `RawTermSubstV2.lift`
  for this instance (the binder shape is the same at the raw
  layer; the dual-lift exists in the typeclass for instances
  where the two MUST diverge).
* `identity` and `compose` are the canonical operations.
* `composeAtHeadIndex` exposes the composed action's effect at a
  single position opaquely; for us it equals
  `subst secondSigma (firstSigma position)` by direct definition.

The four laws:
* `compose_assoc_pointwise`: cite `subst_compose` (#181c6).
  Reduces to `subst s3 (subst s2 (s1 pos)) = subst (compose s2 s3) (s1 pos)`,
  which IS subst_compose applied to `s1 pos`.
* `compose_identity_left_pointwise`: `rfl`.  After unfolding,
  becomes `subst sigma (identity pos) = sigma pos`.  The identity
  substitution at pos is `mkGen .gen_var pos .childNil`; foldV2's
  var arm reduces `subst sigma (mkGen .gen_var pos .childNil)`
  to `sigma pos`.
* `compose_identity_right_pointwise`: cite `subst_identity_apply`
  (#181b).  Reduces to `subst identity (sigma pos) = sigma pos`,
  which IS subst_identity_apply applied to `sigma pos`.
* `headIndex_compose`: `rfl`.  Both sides reduce to
  `subst secondSigma (firstSigma pos)` by compose's definition.
-/
instance instActionRawTermSubstV2 : LeanFX2.Action RawTermSubstV2 where
  ActionTarget       := RawTermV2
  headIndex          := fun someSubstitution position =>
    someSubstitution position
  liftForTy          := fun someSubstitution => someSubstitution.lift
  liftForRaw         := fun someSubstitution => someSubstitution.lift
  identity           := RawTermSubstV2.identity
  compose            := RawTermSubstV2.compose
  composeAtHeadIndex := fun firstSubstitution secondSubstitution position =>
    RawTermV2.subst secondSubstitution (firstSubstitution position)
  compose_assoc_pointwise firstSubstitution middleSubstitution
      lastSubstitution position := by
    -- Goal (after unfolding composeAtHeadIndex on both sides):
    --   subst lastSigma (subst middleSigma (firstSigma pos))
    --   = subst (compose middleSigma lastSigma) (firstSigma pos)
    -- Which is exactly RawTermV2.subst_compose applied at
    -- term = firstSigma pos.
    exact RawTermV2.subst_compose middleSubstitution lastSubstitution
            (firstSubstitution position)
  compose_identity_left_pointwise someSubstitution position := by
    -- Goal (after unfolding composeAtHeadIndex):
    --   subst someSubstitution (identity position) = someSubstitution position
    -- identity position = mkGen .gen_var position .childNil; foldV2's
    -- var arm reduces this to `someSubstitution position`.  Closes
    -- by rfl.
    rfl
  compose_identity_right_pointwise someSubstitution position := by
    -- Goal (after unfolding composeAtHeadIndex):
    --   subst identity (someSubstitution position) = someSubstitution position
    -- Which is RawTermV2.subst_identity_apply (#181b) applied at
    -- term = someSubstitution position.
    exact RawTermV2.subst_identity_apply (someSubstitution position)
  headIndex_compose firstSubstitution secondSubstitution position := by
    -- Goal:
    --   (compose firstSigma secondSigma) position
    --   = composeAtHeadIndex firstSigma secondSigma position
    -- By compose's defn: `(compose firstSigma secondSigma) position =
    --   subst secondSigma (firstSigma position)`.
    -- By composeAtHeadIndex's defn: same expression.  rfl.
    rfl

/-! ## Section 2 — Equivalence theorems

Witness that the manually-named v2 operations agree with the
Action-typeclass-derived operations.  Useful for proofs that
straddle the manual / typeclass API. -/

/-- `RawTermSubstV2.identity` is the Action instance's identity. -/
theorem RawTermSubstV2.identity_eq_action {scope : Nat} :
    (RawTermSubstV2.identity : RawTermSubstV2 scope scope) =
      (LeanFX2.Action.identity : RawTermSubstV2 scope scope) := rfl

/-- `RawTermSubstV2.lift` agrees with the Action instance's
`liftForTy`. -/
theorem RawTermSubstV2.lift_eq_actionForTy
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope) :
    someSubstitution.lift = LeanFX2.Action.liftForTy someSubstitution := rfl

/-- `RawTermSubstV2.lift` agrees with the Action instance's
`liftForRaw`. -/
theorem RawTermSubstV2.lift_eq_actionForRaw
    {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubstV2 sourceScope targetScope) :
    someSubstitution.lift = LeanFX2.Action.liftForRaw someSubstitution := rfl

/-- `RawTermSubstV2.compose` is the Action instance's `compose`. -/
theorem RawTermSubstV2.compose_eq_action
    {sourceScope middleScope targetScope : Nat}
    (firstSubstitution : RawTermSubstV2 sourceScope middleScope)
    (secondSubstitution : RawTermSubstV2 middleScope targetScope) :
    RawTermSubstV2.compose firstSubstitution secondSubstitution =
      LeanFX2.Action.compose firstSubstitution secondSubstitution := rfl

/-! ## Section 3 — Smoke tests

Verify the instance and the equivalence theorems invoke cleanly. -/

/-- Smoke: the Action instance's `headIndex` of identity at any
position returns `mkGen .gen_var pos .childNil`. -/
theorem RawTermSubstV2.action_identity_headIndex_smoke {scope : Nat}
    (position : Fin scope) :
    LeanFX2.Action.headIndex
        (LeanFX2.Action.identity : RawTermSubstV2 scope scope) position =
      (.mkGen .gen_var position .childNil : RawTermV2 scope) := rfl

/-- Smoke: the Action instance's `compose_identity_left` law fires
on a concrete substitution + position 0 of a lifted scope. -/
theorem RawTermSubstV2.action_compose_identity_left_smoke
    {scope : Nat}
    (someSubstitution : RawTermSubstV2 (scope + 1) (scope + 1)) :
    LeanFX2.Action.composeAtHeadIndex
        (LeanFX2.Action.identity : RawTermSubstV2 (scope + 1) (scope + 1))
        someSubstitution
        (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1)) =
      LeanFX2.Action.headIndex someSubstitution
        (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1)) := by
  exact LeanFX2.Action.compose_identity_left_pointwise someSubstitution _

end LeanFX2.Foundation.PolyCell.Core
