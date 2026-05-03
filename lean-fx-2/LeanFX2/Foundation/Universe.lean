/-! # Foundation/Universe — universe hierarchy + cumulativity preorder

This file defines the universe-level syntax and preorder used by the
Day 1 `Ty.universe` constructor.

## Why prepare structurally now

The architectural commitment in `CLAUDE.md` says:
* Cumulativity is a **Conv rule** (Layer 3+), not a Ty constructor
* Universe (`Ty.universe`) IS a Ty constructor when it lands

When `Ty.universe` lands, every match arm in `Ty.rename`, `Ty.subst`,
`Ty.subst_pointwise`, etc. gains one new arm.  By preparing the
preorder and Conv-rule shape NOW, we lock in:
1. The universe levels are non-negative `Nat` (matches Lean 4's Sort
   hierarchy and the Type/Type pitfall avoidance — `level ≤ level+1`
   is the only allowed coercion direction)
2. Cumulativity is **directional** (`u ≤ v → Ty.universe u ⇒ Ty.universe v`),
   never bidirectional
3. The Conv rule is **structural in the level** — no SMT, no decision
   procedure beyond `Nat ≤ Nat` (decidable in core Lean)
4. The Ty.universe ctor will be **additive** — existing ctors remain
   unchanged, downstream match arms gain ONE new case
5. Universe checking happens at **elaboration time** (Algo/Check),
   not in the kernel — the kernel just propagates the level tag

## Universe levels

`UniverseLevel` mirrors the sprint plan's first-order level language:
zero, successor, maximum, and imax.  Level variables and metavariables
are explicitly deferred.

## The universe preorder

`UniverseLevel.le` compares normalized numeric approximations of the finite
level expression.  This keeps the Day 1 hierarchy constructive and decidable;
full symbolic universe constraints belong to the later Lean-kernel encoding.

## Cumulativity (planned `Conv.cumul` rule, Layer 3+)

```lean
| cumul {firstLevel secondLevel : Nat}
        {scope : Nat} {context : Ctx mode firstLevel scope}
        (levelLe : Ty.universeLe firstLevel secondLevel)
        (typeAtLowerLevel : Ty firstLevel scope)
        ... :
    Conv (Ty.cumul levelLe typeAtLowerLevel) typeAtLowerLevel
```

The `Conv.cumul` rule is **definitional** — both sides reduce to the
same canonical form.  This is the MTT formulation: cumulativity is a
silent type coercion, not a runtime computation.

## Phased rollout

* **Day 1**: This file exposes `UniverseLevel`; `Foundation/Ty.lean`
  exposes `Ty.universe`.
* **Later reduction layer**: cumulativity becomes a Conv rule, not a Ty
  coercion constructor.

## Design rationale: why no `Ty : Ty` (Type-in-Type)

Per Girard's paradox: any system with `Ty : Ty` is inconsistent —
allows constructing `False`.  FX's universe hierarchy strictly
stratifies levels (each `Ty.universe N` lives at level `N+1`,
NEVER at level `N`).  This matches Lean 4's `Sort u : Sort (u+1)`.

The `Nat`-indexing means level polymorphism over a *fixed* number of
levels (no unbounded universe variables).  For the canonical FX
fragment, this is sufficient — universe polymorphism for arbitrary
levels would require an additional level-binder constructor (planned
much later if at all).

## Audit gates

Once landed, every Universe-related theorem must pass `#print axioms`
with "does not depend on any axioms" — the universe hierarchy is
constructive (`Nat` operations + structural induction).
-/

namespace LeanFX2

/-- Finite universe-level expressions for the Day 1 hierarchy.

No parameters or metavariables are included in v1.0 kernel syntax; those
belong to the later Lean-kernel meta-verification layer. -/
inductive UniverseLevel : Type
  | zero : UniverseLevel
  | succ (lowerLevel : UniverseLevel) : UniverseLevel
  | max (leftLevel rightLevel : UniverseLevel) : UniverseLevel
  | imax (leftLevel rightLevel : UniverseLevel) : UniverseLevel
  deriving DecidableEq, Repr

namespace UniverseLevel

/-- Interpret finite universe expressions as natural heights.

For the Day 1 syntax fragment, `imax` is represented by the same numeric
upper bound as `max`; the later Lean-kernel encoding will carry Lean's exact
special-case equation for `imax _ 0`. -/
def toNat : UniverseLevel → Nat
  | .zero => 0
  | .succ lowerLevel => lowerLevel.toNat + 1
  | .max leftLevel rightLevel => Nat.max leftLevel.toNat rightLevel.toNat
  | .imax leftLevel rightLevel => Nat.max leftLevel.toNat rightLevel.toNat

/-- Decidable cumulativity preorder on finite universe expressions. -/
@[reducible] def le (lowerLevel upperLevel : UniverseLevel) : Prop :=
  lowerLevel.toNat ≤ upperLevel.toNat

instance leDecidable (lowerLevel upperLevel : UniverseLevel) :
    Decidable (le lowerLevel upperLevel) :=
  Nat.decLe lowerLevel.toNat upperLevel.toNat

/-- Reflexivity of universe cumulativity. -/
theorem le_refl (level : UniverseLevel) : le level level :=
  Nat.le_refl level.toNat

/-- Transitivity of universe cumulativity. -/
theorem le_trans {lowLevel midLevel highLevel : UniverseLevel}
    (lowToMid : le lowLevel midLevel)
    (midToHigh : le midLevel highLevel) :
    le lowLevel highLevel :=
  Nat.le_trans lowToMid midToHigh

/-- Every universe is below its successor. -/
theorem le_succ (level : UniverseLevel) : le level (UniverseLevel.succ level) :=
  Nat.le_succ level.toNat

end UniverseLevel

/-- Nat-level preorder retained for older code paths that have not yet moved
to `UniverseLevel`. -/
@[reducible] def Ty.universeLe (lower upper : Nat) : Prop :=
  lower ≤ upper

/-! ## Preorder laws (free from `Nat.le`'s preorder structure) -/

theorem Ty.universeLe_refl (level : Nat) : Ty.universeLe level level :=
  Nat.le_refl level

theorem Ty.universeLe_trans {lowLevel midLevel highLevel : Nat}
    (lowToMid : Ty.universeLe lowLevel midLevel)
    (midToHigh : Ty.universeLe midLevel highLevel) :
    Ty.universeLe lowLevel highLevel :=
  Nat.le_trans lowToMid midToHigh

/-- Decidability: at elaboration time, comparing two universe levels
is a `Nat`-decidable instance from core Lean.  When `Conv.cumul` is
added (Layer 3+), this enables the elaborator to insert cumulativity
coercions without runtime cost. -/
instance Ty.universeLe_decidable (lower upper : Nat) :
    Decidable (Ty.universeLe lower upper) :=
  Nat.decLe lower upper

/-! ## Successor laws — every level has a unique strict successor

These will be load-bearing for the `Ty.universe N : Ty (N+1) scope`
ctor's typing rule.  When `Ty.universe` lands, the kernel auto-produces
a Ty at the next level — no inference needed. -/

theorem Ty.universeLe_succ (level : Nat) :
    Ty.universeLe level (level + 1) :=
  Nat.le_succ level

theorem Ty.universeLe_succ_iff_le {lower upper : Nat} :
    Ty.universeLe lower (upper + 1) ↔ lower ≤ upper + 1 :=
  Iff.rfl

end LeanFX2
