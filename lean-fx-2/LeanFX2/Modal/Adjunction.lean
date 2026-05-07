/-! # Modal/Adjunction

Day 0 scaffold for modal adjunction theorems.

## Status

**PARTIALLY UNBLOCKED 2026-05-07** (tracker #1329 D4.2).  The
cross-mode `Modality` ctors `Modality.flat` and `Modality.sharp`
now ship in `Modal/Foundation.lean` (Phase 12.A.6 cross-mode
extension); see `Modal/Cohesive.lean` for their uniqueness
theorems.  What remains BLOCKED is the **TwoCell + cross-mode
compose** infrastructure — without those, η/ε are 1-cell label
equalities rather than natural transformations, and the 2-cell
content of an adjunction collapses.

The canonical `◇ ⊣ □` adjunction in modal logic lives across
worlds (cross-mode in our setting).  With cross-mode ctors now
available, expressing `flat ⊣ sharp` in 1-cell language is
possible (see Cohesive's uniqueness theorems), but the
adjunction's natural-transformation structure (η : id ⇒ □ ∘ ◇,
ε : ◇ ∘ □ ⇒ id) requires 2-cells.

Remaining prerequisites before this file can ship its theorems:

1. **TwoCell** type — encodes 2-cells `α : F ⇒ G` between 1-cells.
   Needed to express unit `η : id ⇒ □ ∘ ◇` and counit
   `ε : ◇ ∘ □ ⇒ id` as natural transformations rather than just
   1-cell label equalities.
2. **Cross-mode compose `composeOpen`** — generalising the
   same-mode `compose : Modality m m → Modality m m → Modality m m`
   to `Modality s m → Modality m t → Modality s t`.  Decisions on
   the cross-mode table (e.g. `compose flat sharp = ?`) are
   adjunction-determined; without TwoCells we cannot disambiguate.
   Same-mode `compose` (and its laws — identity, idempotency,
   associativity, absorption) ships clean and remains unaffected.
3. **Modality interpretation** —
   `Modality m1 m2 → (Ty m1 → Ty m2)` so 2-cells become natural
   transformations between interpretations.

## What WILL ship here when prerequisites land

* `Adjoint : Modality m1 m2 → Modality m2 m1 → Prop` — predicate
  characterizing left-adjoint / right-adjoint pairs.
* `flatAdjSharp : Adjoint Modality.flat Modality.sharp` — the
  cohesive flat-sharp adjunction at the kernel layer.
* `diamondAdjBox` — same-mode trivial adjunction (witness via η/ε
  identities), once 2-cells are available to state η and ε as
  natural transformations rather than 1-cell label equalities.
* Triangle identities `(ε □) ∘ (□ η) = id □` and
  `(◇ ε) ∘ (η ◇) = id ◇`.
* Naturality squares for η and ε.

## Deliverable until then

This file remains a documented placeholder.  Adding any theorem
here without the TwoCell prerequisite would either (a) ship a
half-measure that conflates 1-cell equality with 2-cell content,
or (b) introduce a hypothesis-as-postulate (banned by project
zero-axiom commitment, see CLAUDE.md).

The cross-mode handle layer (Cohesive) IS shipped under the new
Modality ctors; only the 2-cell adjunction layer awaits TwoCell.
-/

namespace LeanFX2
namespace Modal

end Modal
end LeanFX2
