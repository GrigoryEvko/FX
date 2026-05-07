/-! # Modal/2LTT — Two-Level Type Theory (integration tests)

Stratify types into two layers:
* **Static layer** — typing-time values, ghost-mode (no runtime
  representation)
* **Dynamic layer** — runtime values: software, hardware, wire

The shipped Layer enum + bounded join-semilattice + preorder +
RespectsLayerSeparation predicate live in `Modal/TwoLevel.lean`
(D4.1, ✅ closed); see that file's docstring for the algebra
catalogue.

## Status

**BLOCKED on Phase 12.A.6+ infrastructure** (tracker #1335 D4.8).
This file is reserved for *integration tests* showing how Layer
discipline composes with concrete modal applications (Ghost / Cap
/ Later / Clock).  Those concrete modal applications are
themselves blocked on cross-mode `Modality` ctors (per
`Modal/Adjunction.lean`'s Phase 12.A.6+ blocker).  Once the
modal-application files (#1334 D4.7) ship, this file fills with
end-to-end tests.

## What WILL ship when prerequisites land

* `ghost ⊣ erase` adjunction integration test using the cross-mode
  `Modality.flat` / `Modality.sharp` from `Modal/Cohesive.lean`.
* `ClassicalContentSeparation` theorem — a signature respects 2LTT
  layer separation iff its modal annotations align with
  `RespectsLayerSeparation`.
* Smoke tests demonstrating that `Term`s living in static vs
  dynamic layer cannot freely mix without an explicit modal
  coercion.

## Dependencies (when shipped)

* `Modal/TwoLevel.lean` (D4.1, ✅) — Layer enum + algebra
* `Modal/Ghost.lean` (D4.7, blocked) — ghost modal application
* `Modal/Adjunction.lean` (D4.2, blocked) — adjunction predicate

## Downstream consumers

* Compilation phases (frontend → static phase + dynamic phase)
* User-level proofs that ghost-mode values are never observed at
  runtime
-/

namespace LeanFX2

end LeanFX2
