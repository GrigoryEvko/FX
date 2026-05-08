/-! # Modal/BoxPath

Day 0 scaffold for the theorem that box commutes with paths.

## Status

**BLOCKED on Phase 12.A.6+ infrastructure** (tracker #1330 D4.3).
The "□ commutes with Path/Id" equivalence requires:

1. **Typed modal Term ctors** — `Term.boxIntro` / `Term.boxElim`
   (or equivalent) shipping as kernel ctors that produce values at
   `Ty.modal Modality.boxK` types.  Foundation has `Ty.modal` (per
   D1.5) but the typed Term layer for modal intro/elim is reserved
   for Phase 12.A.6+.
2. **Path/Id interaction with modalities** — the equivalence
   `□ (Path A x y) ≃ Path (□ A) (boxIntro x) (boxIntro y)` needs
   a `transp`-style commutation, which itself requires the
   substantive cubical β framework (D2.5.1/D2.5.2 deferred).

## What WILL ship when prerequisites land

* `BoxPath.commute : Equiv (□ (Path A x y)) (Path (□ A) (boxIntro x) (boxIntro y))`
* Same for `Ty.id` (HOTT path): `□ (Ty.id A x y) ≃ Ty.id (□ A) (boxIntro x) (boxIntro y)`
* The dual statement for `◇`.

## Deliverable until then

Documented placeholder.  See `Modal/Adjunction.lean` for a fuller
explanation of the same Phase 12.A.6+ infrastructure gap.

## Root status

* Layer: audit-only
* Load-bearing for: none — pure-derivation file (Day 0 scaffold; namespace only)
* Axiom budget: zero (verified via `#assert_no_axioms` in Tools/AuditAll/)
-/

namespace LeanFX2
namespace Modal

end Modal
end LeanFX2
