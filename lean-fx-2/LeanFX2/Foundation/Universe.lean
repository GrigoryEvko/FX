import LeanFX2.Foundation.Ty

/-! # Foundation/Universe — universe hierarchy + cumulativity preorder

**STATUS: Structural scaffolding for FUTURE integration of universe
levels.**  This file defines the universe-level preorder (`Ty.universeLe`)
and the design of `Ty.universe` as a future `Ty` constructor.  No
`Ty.universe` ctor is added yet — see "Phased rollout" below.

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

## The universe preorder

`Ty.universeLe : Nat → Nat → Prop` is just `Nat.le` but exposed at
the Ty namespace for clarity.  Lean's `Nat.le` is decidable + zero-axiom,
so this preorder is computable at elaboration time.

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

* **Now (Phase 1.F)**: This file; `Ty.universeLe` exposed as a
  Decidable preorder.  No `Ty.universe` ctor yet.  Existing kernel
  unchanged.
* **Phase X.Y (TBD)**: `Ty.universe (level : Nat) : Ty (level+1) scope`
  added to the inductive.  All Ty match arms updated (additive — one
  new case each).  ~6 files touched: Ty/RawSubst/Subst/Pointwise/
  Rename/HEqCongr (each gets a `.universe` arm returning `.universe _`).
* **Phase Y.Z (TBD)**: `Conv.cumul` rule added as Conv constructor.
  Decidable per-pair via Nat decidable order.

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

/-- The universe-level preorder.  `Ty.universeLe lower upper` iff
`lower ≤ upper` as naturals — a smaller universe is structurally
contained in a larger one (cumulativity direction).  Reuses Lean's
`Nat.le` for zero-axiom decidability. -/
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
