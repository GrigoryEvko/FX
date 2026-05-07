import LeanFX2.Modal.Cohesive

/-! # Smoke/AuditPhase12A6CohesiveCtors — D4.4 cross-mode ctors reviewer log

Reviewer-facing `#print axioms` log over the new cross-mode
modality handles introduced in Phase 12.A.6 (commit landed
2026-05-07).  Each entry MUST report "does not depend on any
axioms" under strict policy.

## What gets audited

* `LeanFX2.Modality` — the inductive itself (now with five ctors:
  identity / boxK / diamondK / flat / sharp)
* `LeanFX2.Modality.flat` — cross-mode arrow software ⤳ ghost
* `LeanFX2.Modality.sharp` — cross-mode arrow ghost ⤳ software
* `LeanFX2.Modality.flat_uniqueness` — uniqueness of flat at its
  index pair
* `LeanFX2.Modality.sharp_uniqueness` — uniqueness of sharp at its
  index pair

## Why uniqueness matters

The uniqueness theorems are the structural foundation for later
adjoint-chain reasoning: any cross-mode handle in either direction
MUST be the canonical ctor — no anonymous cross-mode modalities
exist at the kernel level.  Proved via full case-on-modality;
impossible-by-index ctors discharged by Lean's structural matcher
without propext (closed-enum Mode.noConfusion).

## Companion gates

* `Smoke/AuditPhase12A5ModalFoundation.lean` — same-mode compose
  laws, unchanged by this extension.
-/

#print axioms LeanFX2.Modality
#print axioms LeanFX2.Modality.flat
#print axioms LeanFX2.Modality.sharp
#print axioms LeanFX2.Modality.flat_uniqueness
#print axioms LeanFX2.Modality.sharp_uniqueness
