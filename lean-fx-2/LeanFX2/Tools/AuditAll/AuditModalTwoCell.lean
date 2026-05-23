import LeanFX2.Tools.DependencyAudit
import LeanFX2.Modal.TwoCellLaws
import LeanFX2.Modal.TwoLevel
import LeanFX2.Modal.Ghost
import LeanFX2.Modal.Cohesive

/-! # AuditModalTwoCell — Modal/TwoCell + Modal/TwoCellLaws gates.

Per-decl `#assert_no_axioms` checks for the 2-cell inductive
(`Modal/TwoCell.lean`, D4.0a #1699) plus the four coherence-law
theorems and the supporting `TwoCellEq` equivalence-relation
inductive (`Modal/TwoCellLaws.lean`, D4.0b #1700).

Per `CLAUDE.md` zero-axiom commitment, every shipped declaration
must report "does not depend on any axioms".  This file is the
machine-enforced gate; `Smoke/AuditPhase12A4TwoCell.lean` is the
matching reviewer-facing log.

The four coherence laws (`vertAssoc`, `vertLeftId`, `vertRightId`,
`exchange`) ship up to the equivalence relation `TwoCellEq` rather
than as Lean propositional equalities — see
`Modal/TwoCellLaws.lean`'s top docstring for the rationale (free
inductive `TwoCell` does not admit these laws as `=`; the proper
mathematical setting is the equivalence relation that quotients
the free 2-cells by the strict-2-category coherence laws). -/

namespace LeanFX2.Tools

/-! ## D4.0a — TwoCell inductive + 3 core ctors -/

#assert_no_axioms LeanFX2.TwoCell
#assert_no_axioms LeanFX2.TwoCell.refl
#assert_no_axioms LeanFX2.TwoCell.vert
#assert_no_axioms LeanFX2.TwoCell.horiz

/-! ## D4.0b — TwoCellEq inductive + 9 ctors -/

#assert_no_axioms LeanFX2.TwoCellEq
#assert_no_axioms LeanFX2.TwoCellEq.reflEq
#assert_no_axioms LeanFX2.TwoCellEq.symmEq
#assert_no_axioms LeanFX2.TwoCellEq.transEq
#assert_no_axioms LeanFX2.TwoCellEq.vertCongEq
#assert_no_axioms LeanFX2.TwoCellEq.horizCongEq
#assert_no_axioms LeanFX2.TwoCellEq.vertAssocEq
#assert_no_axioms LeanFX2.TwoCellEq.vertLeftIdEq
#assert_no_axioms LeanFX2.TwoCellEq.vertRightIdEq
#assert_no_axioms LeanFX2.TwoCellEq.exchangeEq

/-! ## D4.0b — Four coherence-law theorems -/

#assert_no_axioms LeanFX2.TwoCell.vertAssoc
#assert_no_axioms LeanFX2.TwoCell.vertLeftId
#assert_no_axioms LeanFX2.TwoCell.vertRightId
#assert_no_axioms LeanFX2.TwoCell.exchange

/-! ## D4.0c — Modality.composeOpen (cross-mode compose, #1701) -/

#assert_no_axioms LeanFX2.Modality.composeOpen
#assert_no_axioms LeanFX2.Modality.composeOpen_left_identity
#assert_no_axioms LeanFX2.Modality.composeOpen_right_identity
#assert_no_axioms LeanFX2.Modality.composeOpen_boxK_idempotent
#assert_no_axioms LeanFX2.Modality.composeOpen_diamondK_idempotent
#assert_no_axioms LeanFX2.Modality.composeOpen_flat_sharp_cancel
#assert_no_axioms LeanFX2.Modality.composeOpen_sharp_flat_cancel
#assert_no_axioms LeanFX2.Modality.composeOpen_eq_compose_sameMode

/-! ## D4.1 — Modal/TwoLevel: 2LTT layer lattice (Mode→Layer, join,
le) + RespectsLayerSeparation discipline witness.  These were
previously covered only by the reviewer-facing
`Smoke/AuditPhase12A4Day4.lean` log; here is the machine-enforced
per-decl gate. -/

#assert_no_axioms LeanFX2.Layer
#assert_no_axioms LeanFX2.Mode.layer
#assert_no_axioms LeanFX2.Mode.IsStatic
#assert_no_axioms LeanFX2.Mode.IsDynamic
#assert_no_axioms LeanFX2.Mode.layer_dichotomy
#assert_no_axioms LeanFX2.Mode.static_dynamic_disjoint
#assert_no_axioms LeanFX2.Layer.join
#assert_no_axioms LeanFX2.Layer.join_static_left
#assert_no_axioms LeanFX2.Layer.join_static_right
#assert_no_axioms LeanFX2.Layer.join_dynamic_left
#assert_no_axioms LeanFX2.Layer.join_dynamic_right
#assert_no_axioms LeanFX2.Layer.join_comm
#assert_no_axioms LeanFX2.Layer.join_assoc
#assert_no_axioms LeanFX2.Layer.join_idem
#assert_no_axioms LeanFX2.Layer.le
#assert_no_axioms LeanFX2.Layer.le_refl
#assert_no_axioms LeanFX2.Layer.le_trans
#assert_no_axioms LeanFX2.Layer.le_antisymm
#assert_no_axioms LeanFX2.Layer.static_least
#assert_no_axioms LeanFX2.Layer.dynamic_greatest
#assert_no_axioms LeanFX2.Layer.le_join_left
#assert_no_axioms LeanFX2.Layer.le_join_right
#assert_no_axioms LeanFX2.Layer.join_least_upper_bound
#assert_no_axioms LeanFX2.TwoLevel.RespectsLayerSeparation
#assert_no_axioms LeanFX2.TwoLevel.RespectsLayerSeparation.ghost_to_ghost
#assert_no_axioms LeanFX2.TwoLevel.RespectsLayerSeparation.software_to_software
#assert_no_axioms LeanFX2.TwoLevel.RespectsLayerSeparation.ghost_to_software
#assert_no_axioms LeanFX2.TwoLevel.RespectsLayerSeparation.software_to_ghost_violates
#assert_no_axioms LeanFX2.TwoLevel.RespectsLayerSeparation.refl
#assert_no_axioms LeanFX2.TwoLevel.RespectsLayerSeparation.trans

/-! ## D4.x — Modal/Ghost: ghost-mode endo-modality + idempotency
and identity-compose laws. -/

#assert_no_axioms LeanFX2.Modality.ghost
#assert_no_axioms LeanFX2.Modality.ghost_idempotent
#assert_no_axioms LeanFX2.Modality.ghost_compose_identity_right
#assert_no_axioms LeanFX2.Modality.ghost_compose_identity_left
#assert_no_axioms LeanFX2.Modality.ghost_absorbs_diamond

/-! ## D4.4 — Modal/Cohesive: flat ⊣ sharp adjoint uniqueness.
Previously covered only by `Smoke/AuditPhase12A6CohesiveCtors.lean`. -/

#assert_no_axioms LeanFX2.Modality.flat_uniqueness
#assert_no_axioms LeanFX2.Modality.sharp_uniqueness

end LeanFX2.Tools
