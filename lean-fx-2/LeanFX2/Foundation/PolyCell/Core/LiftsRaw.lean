import LeanFX2.Foundation.Action

/-! # Foundation/PolyCell/Core/LiftsRaw — minimal binder-lift typeclass

This file ships `LiftsRaw`, the minimal Allais-fold typeclass: just
the `liftForRaw` operation that foldV2 (#177) needs at binder
crossings.

## Why a separate typeclass from `Action`

The existing `Action` typeclass (Foundation/Action.lean) bundles
FOUR concerns:

1. **Variable lookup** (`headIndex`, `ActionTarget`)
2. **Binder lift** (`liftForRaw`, `liftForTy`)
3. **Monoid structure** (`identity`, `compose`, `composeAtHeadIndex`)
4. **Laws** (`compose_assoc_pointwise`, `compose_identity_*_pointwise`,
   `headIndex_compose`)

foldV2 (#177) uses ONLY concern 2 (specifically `liftForRaw`).
Demanding `[Action Container]` from foldV2 over-constrains the
producer: a Container with only `liftForRaw` could drive foldV2 but
can't currently be plugged in because the type class requires the
other three concerns.

This matters concretely for `RawTermSubstV2` (#180):
* `RawTermSubstV2.compose` semantically requires `RawTermV2.subst`
  (it's `fun s1 s2 pos => (s1 pos).subst s2`)
* `RawTermV2.subst` is what we want to DEFINE via foldV2
* Therefore the Action instance for `RawTermSubstV2` needs `subst`,
  but `subst` needs the Action instance.  Chicken and egg.

The resolution: extract `LiftsRaw` as a smaller typeclass with only
`liftForRaw`.  foldV2 requires `[LiftsRaw Container]`.
`RawTermSubstV2` ships `LiftsRaw` immediately (no compose needed).
`RawTermV2.subst` is then defined via foldV2.  The full `Action`
instance for `RawTermSubstV2` ships LATER (V2-L2.7 / #181) once
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

This is the SOLE typeclass requirement foldV2 (#177) places on its
Container input.  Any data structure that knows how to extend itself
under a binder qualifies — renamings (`RawRenaming` via Action
bridge), substitutions (`RawTermSubstV2` via direct instance), and
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
via v1's `Foundation/RawSubst/ActionInstances`).  foldV2 callers
using `RawRenaming` get the `LiftsRaw` instance synthesized via this
bridge without needing to ship a separate explicit instance. -/
instance instLiftsRawOfAction {Container : Nat → Nat → Type}
    [LeanFX2.Action Container] : LiftsRaw Container where
  liftForRaw := LeanFX2.Action.liftForRaw

end LeanFX2.Foundation.PolyCell.Core
