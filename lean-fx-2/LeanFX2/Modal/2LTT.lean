import LeanFX2.Modal.Ghost

/-! # Modal/2LTT — Two-Level Type Theory

Stratify types into two layers:
* **Static layer** — typing-time values, ghost-mode (no runtime
  representation)
* **Dynamic layer** — runtime values: software, hardware, wire

```lean
inductive Layer
  | static  -- ghost mode
  | dynamic -- software/hardware/wire modes
```

## Adjunction

`ghost ⊣ erase` from `Modal/Ghost.lean`.  Captures the static-
dynamic separation formally.

## Classical-content separation theorem

A signature is "classical-content respecting" iff it produces
values whose types respect the static-dynamic separation:
no static value depends on dynamic value, no dynamic value depends
on a propositionally-fictitious static value.

```lean
theorem ClassicalContentSeparation : ...
```

## Dependencies

* `Modal/Ghost.lean`

## Downstream consumers

* Compilation phases (frontend → static phase + dynamic phase)
-/

namespace LeanFX2

end LeanFX2
