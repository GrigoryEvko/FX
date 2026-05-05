/-! # Modal/Later — Later modality (▶)

The Later modality `▶` enables productive corecursion / guarded
recursion.  `▶ A` is "A available later"; `next : A → ▶ A` is the
introduction.

## Modality declaration

```lean
def Modality.later : Modality := ...
```

## Operations

* `next : A → ▶ A`
* `(<*>) : ▶ (A → B) → ▶ A → ▶ B`  -- applicative-style
* `fix : (▶ A → A) → A`  -- guarded fixed point

## Why ▶

Coinductive types and corecursion are notoriously hard in MLTT.
The ▶ modality (after Atkey-McBride 2013) gives a safe interface:
recursive references are guarded by `next`, ensuring productivity.

## Smoke

`Productive corecursion via setoid encoding` (lean-fx task v3.28).
Build a productive stream type using `▶` and verify it computes.

## Clock quantification

For full guarded recursion we need *clock quantification*:

```lean
def AllClock (A : Clock → Type) : Type := ∀ κ, A κ
```

Defined in `Modal/Clock.lean`.

## Dependencies

* `Modal/Foundation.lean`

## Downstream consumers

* User-level corecursion / streams
- `Modal/Bridge.lean` (uses Later infrastructure conceptually)

## Implementation plan (Phase 7)

1. Define Later modality + intro/elim
2. Verify productivity smoke: 1 + 2 + 4 + ... bitstream
-/

namespace LeanFX2

end LeanFX2
