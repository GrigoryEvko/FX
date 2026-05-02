import LeanFX2.Modal.Later

/-! # Modal/Clock — clock quantification

Clock quantification `∀κ.A` (universally quantify over clocks)
provides the unfolding lemma for guarded fixed points.

```lean
def AllClock {Clock} (A : Clock → Type) : Type := ∀ κ, A κ
```

Combined with `▶` (`Modal/Later.lean`), enables encoding of
coinductive types as `∀κ. (▶^κ A → A)` — a safe corecursion
principle.

## Smoke

Verify productive corecursion (lean-fx task v3.28).

## Dependencies

* `Modal/Later.lean`

## Downstream consumers

* User-level coinductive definitions (streams, infinite trees)
-/

namespace LeanFX2

end LeanFX2
