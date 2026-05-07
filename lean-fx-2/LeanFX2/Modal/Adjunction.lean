/-! # Modal/Adjunction

Day 0 scaffold for modal adjunction theorems.

## Status

**BLOCKED on Phase 12.A.6+ infrastructure** (tracker #1329 D4.2,
reopened 2026-05-07).  The canonical `◇ ⊣ □` adjunction in modal
logic lives across worlds (cross-mode in our setting); the
same-mode `Modality : Mode → Mode → Type` shipped in
`Modal/Foundation.lean` (with only `.identity / .boxK / .diamondK`
endomorphic ctors) is degenerate for adjunction.

Required prerequisites before this file can ship its theorems:

1. **TwoCell** type — encodes 2-cells `α : F ⇒ G` between 1-cells.
   Needed to express unit `η : id ⇒ □ ∘ ◇` and counit
   `ε : ◇ ∘ □ ⇒ id` as natural transformations rather than just
   1-cell label equalities.
2. **Cross-mode `Modality` ctors** — `.flat` (♭ : runtime → ghost),
   `.sharp` (♯ : ghost → runtime), `.later` (▶ : same mode,
   temporal shift), `.bridge` (software → bridge).  Documented
   in `Modal/Foundation.lean` docstring as "Phase 12.A.6+".
3. **Modality interpretation** —
   `Modality m1 m2 → (Ty m1 → Ty m2)` so 2-cells become natural
   transformations between interpretations.

## What WILL ship here when Phase 12.A.6+ lands

* `Adjoint : Modality m1 m2 → Modality m2 m1 → Prop` — predicate
  characterizing left-adjoint / right-adjoint pairs.
* `diamondAdjBox` — same-mode trivial adjunction (witness via η/ε
  identities), once 2-cells are available to state η and ε as
  natural transformations rather than 1-cell label equalities.
* Triangle identities `(ε □) ∘ (□ η) = id □` and
  `(◇ ε) ∘ (η ◇) = id ◇`.
* Naturality squares for η and ε.

## Deliverable until then

This file remains a documented placeholder.  Adding any theorem
here without the TwoCell + cross-mode prerequisites would either
(a) ship a half-measure that conflates 1-cell equality with 2-cell
content, or (b) introduce a hypothesis-as-postulate (banned by
project zero-axiom commitment, see CLAUDE.md).
-/

namespace LeanFX2
namespace Modal

end Modal
end LeanFX2
