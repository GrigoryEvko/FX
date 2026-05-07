/-! # Bridge/BoxObservational

Day 0 scaffold for box commuting with observational identity.

## Status

**BLOCKED on Phase 12.A.6+ infrastructure** (tracker #1390 D9.6).
The "□ commutes with `Ty.id`" claim is a modal-observational
coherence statement that requires:

1. **Typed modal Term ctors** — `Term.boxIntro` / `Term.boxElim`
   producing values at `Ty.modal Modality.boxK` types.
   Foundation has `Ty.modal` (D1.5 ✓) but the typed Term layer
   for modal intro/elim is reserved for Phase 12.A.6+.
2. **Cross-mode `Modality` ctors** — `Modality.boxK` and the
   adjoint pair currently exist only same-mode; the
   commutation-with-Id statement quantifies over modal types
   parameterised by mode-bridging modalities, which become
   well-formed only after `Modal/Cohesive.lean` lands its
   `Modality.flat` / `Modality.sharp` cross-mode ctors.

## What WILL ship when prerequisites land

* `BoxObservational.commute :
    Equiv (Term.box (Ty.id A x y)) (Ty.id (Term.box A) (boxIntro x) (boxIntro y))`
* The dual statement for `◇`.
* Naturality of the equivalence in `A` / `x` / `y`.

## Deliverable until then

Documented placeholder.  See `Modal/Adjunction.lean` for the full
Phase 12.A.6+ prerequisite catalogue; this file is one of the
downstream consumers.
-/

namespace LeanFX2
namespace Bridge

end Bridge
end LeanFX2
