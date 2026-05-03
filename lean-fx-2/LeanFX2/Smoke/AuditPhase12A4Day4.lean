import LeanFX2.Modal.Foundation
import LeanFX2.Modal.TwoLevel

/-! # AuditPhase12A4Day4 — Day 4 (Phase 12.A.4) zero-axiom audit.

Day 4 of the cubical+2LTT+HOTT sprint shipped the modal foundation
plus the 2LTT layer-separation theory:

* D4.1 — Modal/TwoLevel.lean: 2LTT layer enum + Mode-to-Layer
  projection + bounded join-semilattice algebra + Layer preorder
  + LUB property + RespectsLayerSeparation predicate (this commit
  closes D4.1)
* D4.2 — Modal/Adjunction.lean (◇ ⊣ □ unit/counit) — pending
* D4.3 — Modal/BoxPath.lean (□ commutes with Path/Id) — pending
* D4.4 — Modal/Cohesive.lean (♭ / ♯ pair) — pending
* D4.5 — full ♭ ⊣ ◇ ⊣ □ ⊣ ♯ chain — pending
* D4.6 — Modal/Bridge.lean (mode-bridge equivalences) — pending
* D4.7 — Modal/{Ghost,Cap,Later,Clock}.lean — stubs only (4 modal
  application namespaces; concrete content lands per-need)
* D4.8 — Modal/2LTT.lean — stub (concrete tests fold into D4.1
  TwoLevel.lean); future expansion lands when Layer 6 typed Term
  modal ctors arrive
* D4.9 — THIS audit, plus Phase 12.A.4 commit

Modal/Foundation.lean (Phase 12.A.5 sister-file: same-mode
modalities + composition algebra) is audited separately in
`AuditPhase12A5ModalFoundation.lean`; we re-list the entries
here for an integrated Day-4 picture.

Every declaration listed must report "does not depend on any axioms".
The 215+-job project build implicitly verifies the same — this file
explicitly enumerates the Day-4 deliverables for traceability.
-/

-- D4.1 — Layer enum + Mode-to-Layer projection
#print axioms LeanFX2.Layer
#print axioms LeanFX2.Mode.layer
#print axioms LeanFX2.Mode.IsStatic
#print axioms LeanFX2.Mode.IsDynamic

-- D4.1 — Mutual exclusivity / exhaustiveness / decidability
#print axioms LeanFX2.Mode.layer_dichotomy
#print axioms LeanFX2.Mode.static_dynamic_disjoint
#print axioms LeanFX2.Mode.IsStatic.decidable
#print axioms LeanFX2.Mode.IsDynamic.decidable

-- D4.1 — Layer.join (bounded join-semilattice)
#print axioms LeanFX2.Layer.join
#print axioms LeanFX2.Layer.join_static_left
#print axioms LeanFX2.Layer.join_static_right
#print axioms LeanFX2.Layer.join_dynamic_left
#print axioms LeanFX2.Layer.join_dynamic_right
#print axioms LeanFX2.Layer.join_comm
#print axioms LeanFX2.Layer.join_assoc
#print axioms LeanFX2.Layer.join_idem

-- D4.1 — Layer.le (preorder)
#print axioms LeanFX2.Layer.le
#print axioms LeanFX2.Layer.le_refl
#print axioms LeanFX2.Layer.le_trans
#print axioms LeanFX2.Layer.le_antisymm
#print axioms LeanFX2.Layer.static_least
#print axioms LeanFX2.Layer.dynamic_greatest

-- D4.1 — Join is the LUB of the preorder
#print axioms LeanFX2.Layer.le_join_left
#print axioms LeanFX2.Layer.le_join_right
#print axioms LeanFX2.Layer.join_least_upper_bound

-- D4.1 — RespectsLayerSeparation (2LTT discipline witness)
#print axioms LeanFX2.TwoLevel.RespectsLayerSeparation
#print axioms LeanFX2.TwoLevel.RespectsLayerSeparation.ghost_to_ghost
#print axioms LeanFX2.TwoLevel.RespectsLayerSeparation.software_to_software
#print axioms LeanFX2.TwoLevel.RespectsLayerSeparation.ghost_to_software
#print axioms LeanFX2.TwoLevel.RespectsLayerSeparation.software_to_ghost_violates
#print axioms LeanFX2.TwoLevel.RespectsLayerSeparation.refl
#print axioms LeanFX2.TwoLevel.RespectsLayerSeparation.trans

-- Sister-file (Phase 12.A.5) — Modal/Foundation.lean modality 1-cells
-- (re-listed here for an integrated Day-4 picture)
#print axioms LeanFX2.Modality
#print axioms LeanFX2.Modality.compose
#print axioms LeanFX2.Modality.compose_identity_left
#print axioms LeanFX2.Modality.compose_identity_right
#print axioms LeanFX2.Modality.compose_boxK_idempotent
#print axioms LeanFX2.Modality.compose_diamondK_idempotent
#print axioms LeanFX2.Modality.compose_boxK_absorbs_left
#print axioms LeanFX2.Modality.compose_assoc
