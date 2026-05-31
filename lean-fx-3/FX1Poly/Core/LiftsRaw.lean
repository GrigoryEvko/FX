import FX1Poly.Foundation.Action

/-! # Foundation/PolyCell/Core/LiftsRaw — minimal binder-lift typeclass

`LiftsRaw`, the minimal Allais-fold typeclass: just the
`liftForRaw` operation that fold needs at binder crossings.

## Why a separate typeclass from `Action`

The existing `Action` typeclass (Foundation/Action.lean) bundles
FOUR concerns:

1. **Variable lookup** (`headIndex`, `ActionTarget`)
2. **Binder lift** (`liftForRaw`, `liftForTy`)
3. **Monoid structure** (`identity`, `compose`, `composeAtHeadIndex`)
4. **Laws** (`compose_assoc_pointwise`, `compose_identity_*_pointwise`,
   `headIndex_compose`)

fold uses ONLY concern 2 (specifically `liftForRaw`).  Demanding
`[Action Container]` from fold over-constrains the producer: a
Container with only `liftForRaw` could drive fold but couldn't be
plugged in if the typeclass required the other three concerns.

This matters concretely for `RawTermSubst`:
* `RawTermSubst.compose` semantically requires `RawTerm.subst`
  (it's `fun s1 s2 pos => (s1 pos).subst s2`)
* `RawTerm.subst` is itself DEFINED via fold
* So the Action instance for `RawTermSubst` needs `subst`, but
  `subst` needs the Action instance.  Chicken and egg.

The resolution: `LiftsRaw` is a smaller typeclass with only
`liftForRaw`.  fold requires `[LiftsRaw Container]`.  `RawTermSubst`
carries `LiftsRaw` directly (no compose needed); `RawTerm.subst` is
then defined via fold.  The full `Action` instance for
`RawTermSubst` lives in `RawTermSubstAction.lean`.

## Auto-derive bridge from Action

To cover existing Action-instanced types (`RawRenaming` via
`Foundation/RawSubst/ActionInstances.lean`), this file provides an
automatic bridge:

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

namespace FX1Poly.Core

/-- Minimal binder-lift typeclass: lift a Container through one
binder crossing.

This is the SOLE typeclass requirement fold places on its
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

This covers `RawRenaming` (which has `Action` via
`Foundation/RawSubst/ActionInstances`).  fold callers using
`RawRenaming` get the `LiftsRaw` instance synthesized via this
bridge without needing a separate explicit instance. -/
instance instLiftsRawOfAction {Container : Nat → Nat → Type}
    [FX1Poly.Foundation.Action Container] : LiftsRaw Container where
  liftForRaw := FX1Poly.Foundation.Action.liftForRaw

end FX1Poly.Core
