/-! # Bridge/BoxCubical

Day 0 scaffold for box commuting with cubical paths.

## Status

**BLOCKED on Phase 12.A.6+ infrastructure** (tracker #1391 D9.7).
The "□ commutes with `Ty.path`" claim is a modal-cubical coherence
statement that requires:

1. **Typed modal Term ctors** — `Term.boxIntro` / `Term.boxElim`
   producing values at `Ty.modal Modality.boxK` types
   (same prerequisite as `Bridge/BoxObservational.lean`).
2. **Cubical Path interaction with modalities** — the equivalence
   `□ (Path A x y) ≃ Path (□ A) (boxIntro x) (boxIntro y)` requires
   either a `transp`-style commutation step (D2.5.1 typed
   transpBeta — strategically deferred per
   `Smoke/AuditPhase12A2Day2.lean`) or a direct cubical
   universe-path eliminator (not in this kernel slice).
3. **Cross-mode `Modality`** — same constraint as
   `BoxObservational.lean`; `Modality.box` must be available
   in mode-bridging form for the equivalence to type-check.

## What WILL ship when prerequisites land

* `BoxCubical.commute :
    Equiv (Term.box (Ty.path A x y))
          (Ty.path (Term.box A) (boxIntro x) (boxIntro y))`
* The corresponding statement for `Ty.id` lives in
  `Bridge/BoxObservational.lean` (sibling D9.6).
* The dual statement for `◇`.

## Deliverable until then

Documented placeholder.  See `Modal/Adjunction.lean` for the full
Phase 12.A.6+ prerequisite catalogue, and `Modal/BoxPath.lean` for
the parallel observational-side blocker analysis.
-/

namespace LeanFX2
namespace Bridge

end Bridge
end LeanFX2
