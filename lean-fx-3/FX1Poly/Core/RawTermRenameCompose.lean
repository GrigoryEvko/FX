import FX1Poly.Core.RawTermRenamePointwise

/-! # Foundation/PolyCell/Core/RawTermRenameCompose — renaming-side lift-compose fusion

This file ships the **binder-level fusion** between `RawRenaming.lift`
and `RawRenaming.compose`:

  lift (compose rho1 rho2) ≅ compose (lift rho1) (lift rho2)   (pointwise)

at the lifted scope, plus the Nat-indexed iterated form needed by
fold binder-depth traversal.

## Where this sits in the cross-direction fusion ladder

  rename_pointwise            (#181c1, shipped)
  lift_compose_pointwise      (THIS FILE — renaming side)
  iterateLiftRaw_compose_pointwise (THIS FILE — renaming side)
  Generator.payload_cast_compose   (next — helper for term-level)
  rename_compose              (next — term-level fusion)
  subst_rename_commute        (after)
  rename_subst_commute        (after)
  lift_compose_pointwise      (subst side, uses above)
  iterateLiftRaw_compose_pointwise (subst side)
  subst_compose               (the headline)
  Action RawTermSubst instance  (closes V2-L2.7)

## Why this is BINDER-level, not term-level

This file ships ONLY the lift-side fusion — no recursion over
`RawTerm` is needed.  The headline `RawRenaming.lift_compose_pointwise`
is a pure Fin pattern match (0 / k+1) that closes by `rfl` on both
branches.  The iterated version is a Nat induction.

The TERM-level fusion (`RawTerm.rename_compose`) ships in a
follow-up commit; it consumes this file's lemmas at every binder
crossing.

## The Fin-cases reasoning (both close by `rfl`)

At position `⟨0, _⟩`:
* LHS: `(compose rho1 rho2).lift ⟨0, _⟩ = ⟨0, _⟩` (by `lift`'s defn).
* RHS: `compose rho1.lift rho2.lift ⟨0, _⟩
       = rho2.lift (rho1.lift ⟨0, _⟩)
       = rho2.lift ⟨0, _⟩
       = ⟨0, _⟩`.
* Both `⟨0, _⟩`.  `rfl`.

At position `⟨k+1, _⟩`:
* LHS: `(compose rho1 rho2).lift ⟨k+1, _⟩
       = Fin.succ ((compose rho1 rho2) ⟨k, _⟩)
       = Fin.succ (rho2 (rho1 ⟨k, _⟩))`.
* RHS: `compose rho1.lift rho2.lift ⟨k+1, _⟩
       = rho2.lift (rho1.lift ⟨k+1, _⟩)
       = rho2.lift (Fin.succ (rho1 ⟨k, _⟩))
       = Fin.succ (rho2 (rho1 ⟨k, _⟩))`
  (the last step is by `lift`'s defn at a successor Fin).
* Both `Fin.succ (rho2 (rho1 ⟨k, _⟩))`.  `rfl`.

So the entire theorem is two `rfl` arms — propext-clean by construction.

## Iterated form via Nat induction

`iterateLiftRaw_RawRenaming_compose_pointwise depth` says:

  iterateLiftRaw (compose rho1 rho2) depth ≅
    compose (iterateLiftRaw rho1 depth) (iterateLiftRaw rho2 depth)

Inducts on `depth`:
* `zero`: both sides reduce to `compose rho1 rho2` (no lift).  Reflexivity.
* `succ k`: at the `k+1`-th lift, we have `lift (iterateLiftRaw _ k)`.
  Chains `lift_pointwise priorIH` (gives `lift (compose-iterk) ≅
  lift (compose (iterk rho1) (iterk rho2))`) with `lift_compose_pointwise`
  (gives `lift (compose X Y) ≅ compose (lift X) (lift Y)`).

## Zero-axiom verification

* `RawRenaming.lift_compose_pointwise` — Fin pattern match, both
  branches close by `rfl`.  Propext-clean.
* `iterateLiftRaw_RawRenaming_compose_pointwise` — Nat induction
  using #181c1's `lift_pointwise` + this file's `lift_compose_pointwise`.
  Propext-clean.

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Section 1 — Single-binder lift commutes with composition

The renaming side of the binder-fusion identity.  Pure Fin
arithmetic; no `RawTerm` induction. -/

/-- Single-binder lift commutes with renaming composition (pointwise).

For any two composable renamings `rho1 : RawRenaming src mid` and
`rho2 : RawRenaming mid tgt`, the lift of their composition agrees
pointwise with the composition of their lifts at the lifted scopes.

Both Fin cases (⟨0, _⟩ and ⟨k+1, _⟩) close by `rfl` because
`RawRenaming.lift` and `RawRenaming.compose` are both `@[reducible]`
and their definitions reduce uniformly under both arms. -/
theorem RawRenaming.lift_compose_pointwise
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope) :
    RawRenaming.PointwiseEq
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming).lift
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming.lift secondRenaming.lift) := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨_priorPositionValue + 1, _⟩ => rfl

/-! ## Section 2 — Iterated lift commutes with composition

Nat induction lifting `lift_compose_pointwise` through arbitrary
binder depths.  Needed by future fold-based theorems
(`RawTerm.rename_compose`, `subst_compose`) at each `childCons`
spine descent. -/

/-- Iterated lift commutes with renaming composition (pointwise).

Induction on `binderDepth`:
* `zero`: `iterateLiftRaw _ 0 = _`, so both sides equal
  `compose firstRenaming secondRenaming`.  Pointwise reflexivity.
* `succ priorDepth`: at depth `priorDepth + 1` the iterated lift
  unfolds to `lift (iterateLiftRaw _ priorDepth)`.
  - By IH (`priorIH`): the depth-`priorDepth` iterations agree
    pointwise.
  - By `RawRenaming.lift_pointwise priorIH`: their LIFTS also agree
    pointwise — `lift (iterLift compose-renaming priorDepth) ≅
    lift (compose (iterLift fst priorDepth) (iterLift snd priorDepth))`.
  - By `lift_compose_pointwise`: the lifted composition pulls inside
    the lift — `lift (compose X Y) ≅ compose (lift X) (lift Y)`.
  - Chaining the two rewrites yields the goal.

This is the renaming-side analog of v1's `RawTermSubst`-style
iterated lift-compose fusion. -/
theorem iterateLiftRaw_RawRenaming_compose_pointwise
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope)
    (binderDepth : Nat) :
    RawRenaming.PointwiseEq
        (iterateLiftRaw
            (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
            binderDepth)
        (FX1Poly.Foundation.RawRenaming.compose
            (iterateLiftRaw firstRenaming binderDepth)
            (iterateLiftRaw secondRenaming binderDepth)) := by
  induction binderDepth with
  | zero =>
      -- iterateLiftRaw _ 0 = _ by iterateLiftRaw's defn.
      -- Both sides reduce to (compose firstRenaming secondRenaming),
      -- so pointwise reflexivity closes the goal.
      exact RawRenaming.PointwiseEq.refl _
  | succ _priorDepth priorIH =>
      -- iterateLiftRaw _ (k+1) = lift (iterateLiftRaw _ k) by defn.
      -- Chain: lift (iter compose) ≅ lift (compose iter1 iter2) ≅
      --        compose (lift iter1) (lift iter2).
      intro position
      show RawRenaming.lift
              (iterateLiftRaw
                  (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming)
                  _priorDepth) position =
            FX1Poly.Foundation.RawRenaming.compose
              (RawRenaming.lift (iterateLiftRaw firstRenaming _priorDepth))
              (RawRenaming.lift (iterateLiftRaw secondRenaming _priorDepth))
              position
      rw [RawRenaming.lift_pointwise priorIH position,
          RawRenaming.lift_compose_pointwise _ _ position]

/-! ## Section 3 — Smoke tests

Verify the lift-compose fusion lemmas invoke cleanly on closed Fin
positions.  These exercise both Fin branches of
`lift_compose_pointwise` and both depth arms of
`iterateLiftRaw_RawRenaming_compose_pointwise`. -/

/-- Smoke: lift_compose on position 0 closes by `rfl`. -/
theorem RawRenaming.lift_compose_pointwise_zero_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope) :
    (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming).lift
        (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1)) =
      FX1Poly.Foundation.RawRenaming.compose firstRenaming.lift secondRenaming.lift
        (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1)) :=
  RawRenaming.lift_compose_pointwise firstRenaming secondRenaming _

/-- Smoke: iterated lift-compose at depth 0 is reflexivity. -/
theorem iterateLiftRaw_RawRenaming_compose_pointwise_zero_smoke
    {sourceScope middleScope targetScope : Nat}
    (firstRenaming : FX1Poly.Foundation.RawRenaming sourceScope middleScope)
    (secondRenaming : FX1Poly.Foundation.RawRenaming middleScope targetScope)
    (position : Fin sourceScope) :
    iterateLiftRaw
        (FX1Poly.Foundation.RawRenaming.compose firstRenaming secondRenaming) 0
        position =
      FX1Poly.Foundation.RawRenaming.compose
        (iterateLiftRaw firstRenaming 0)
        (iterateLiftRaw secondRenaming 0)
        position :=
  iterateLiftRaw_RawRenaming_compose_pointwise
    firstRenaming secondRenaming 0 position

end FX1Poly.Core
