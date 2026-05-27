import LeanFX2.Foundation.Action

/-! # Foundation/PolyCell/Core/LiftsRaw — minimal binder-lift typeclass

This file ships `LiftsRaw`, the minimal Allais-fold typeclass: just
the `liftForRaw` operation that fold (#177) needs at binder
crossings.

## Why a separate typeclass from `Action`

The existing `Action` typeclass (Foundation/Action.lean) bundles
FOUR concerns:

1. **Variable lookup** (`headIndex`, `ActionTarget`)
2. **Binder lift** (`liftForRaw`, `liftForTy`)
3. **Monoid structure** (`identity`, `compose`, `composeAtHeadIndex`)
4. **Laws** (`compose_assoc_pointwise`, `compose_identity_*_pointwise`,
   `headIndex_compose`)

fold (#177) uses ONLY concern 2 (specifically `liftForRaw`).
Demanding `[Action Container]` from fold over-constrains the
producer: a Container with only `liftForRaw` could drive fold but
can't currently be plugged in because the type class requires the
other three concerns.

This matters concretely for `RawTermSubst` (#180):
* `RawTermSubst.compose` semantically requires `RawTerm.subst`
  (it's `fun s1 s2 pos => (s1 pos).subst s2`)
* `RawTerm.subst` is what we want to DEFINE via fold
* Therefore the Action instance for `RawTermSubst` needs `subst`,
  but `subst` needs the Action instance.  Chicken and egg.

The resolution: extract `LiftsRaw` as a smaller typeclass with only
`liftForRaw`.  fold requires `[LiftsRaw Container]`.
`RawTermSubst` ships `LiftsRaw` immediately (no compose needed).
`RawTerm.subst` is then defined via fold.  The full `Action`
instance for `RawTermSubst` ships LATER (V2-L2.7 / #181) once
`subst` exists.

## Auto-derive bridge from Action

To preserve compatibility with existing Action-instanced types
(`RawRenaming` via v1's `Foundation/RawSubst/ActionInstances.lean`),
this file provides an automatic bridge:

```
instance [Action Container] : LiftsRaw Container where
  liftForRaw := Action.liftForRaw
```

Existing `Action` instances automatically satisfy `LiftsRaw` via this
bridge.  No need to ship duplicate instances per Container.

## Zero-axiom verification

* `LiftsRaw` — single-field typeclass (no equation lemmas)
* Action bridge instance — projection through Action.liftForRaw

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Minimal binder-lift typeclass: lift a Container through one
binder crossing.

This is the SOLE typeclass requirement fold (#177) places on its
Container input.  Any data structure that knows how to extend itself
under a binder qualifies — renamings (`RawRenaming` via Action
bridge), substitutions (`RawTermSubst` via direct instance), and
any future Container shape. -/
class LiftsRaw (Container : Nat → Nat → Type) where
  /-- Lift the Container through one binder crossing, extending both
  source and target scopes by one. -/
  liftForRaw : {sourceScope targetScope : Nat} →
                  Container sourceScope targetScope →
                  Container (sourceScope + 1) (targetScope + 1)

/-- Automatic bridge: any `Action`-instanced Container automatically
satisfies `LiftsRaw` by projecting through `Action.liftForRaw`.

This preserves compatibility with `RawRenaming` (which has `Action`
via v1's `Foundation/RawSubst/ActionInstances`).  fold callers
using `RawRenaming` get the `LiftsRaw` instance synthesized via this
bridge without needing to ship a separate explicit instance. -/
instance instLiftsRawOfAction {Container : Nat → Nat → Type}
    [LeanFX2.Action Container] : LiftsRaw Container where
  liftForRaw := LeanFX2.Action.liftForRaw

end LeanFX2.Foundation.PolyCell.Core
