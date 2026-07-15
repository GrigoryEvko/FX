import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.ModeRelativeMetatheory

/-! # FX1PolyAudit/AuditAxisModeRelativeMetatheory — zero-axiom gate for mode-9

Per-declaration zero-axiom gate for `mode-9` (`FX1Poly/Axis/Mode/ModeRelativeMetatheory.lean`): the
computad→ωcE word encoding (the dimension-1 bridge) + its monoid homomorphism / length / distinguisher, the
faithful-tagging dimension-1 word-problem DECISION (reusing the ωcE word `DecidableEq` via `decidable_of_iff`),
the concrete adjunction tagging, the trivial-mode canonicity base, the mode-relative parameter, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The computad → ωcE word encoding (the dimension-1 bridge)
#assert_no_axioms FX1Poly.Axis.ComputadGeneratorTagging
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.encodeSlots
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.encodeWordCode
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.encodeSlots_composePath
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.encodeWordCode_composePath
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.encodeWordCode_identityPath
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.encodeWordCode_length
#assert_no_axioms FX1Poly.Polygraph.ModalityPath.ne_of_encodeWordCode_ne

-- The dimension-1 word problem DECIDED (reusing the ωcE word DecidableEq)
#assert_no_axioms FX1Poly.Axis.FaithfulComputadTagging
#assert_no_axioms FX1Poly.Axis.FaithfulComputadTagging.decidableOneCellEq

-- The concrete adjunction tagging + the computed encoding
#assert_no_axioms FX1Poly.Axis.adjunctionTagging
#assert_no_axioms FX1Poly.Axis.adjunctionLeftThenRight_encodeWordCode

-- Multimodal canonicity (the trivial-mode base) + the mode-relative parameter
#assert_no_axioms FX1Poly.Axis.trivialComputad_oneCell_length_zero
#assert_no_axioms FX1Poly.Axis.trivialComputad_oneCell_unique
#assert_no_axioms FX1Poly.Axis.trivialFaithfulComputadTagging
#assert_no_axioms FX1Poly.Polygraph.Computad.modeRelativeParameter

-- The SATURATED mode-relative decision at the walking adjunction (scoped, backed by the shipped decision)
#assert_no_axioms FX1Poly.Axis.adjunctionSaturatedModeRelativeConvDecision

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasMultimodalCanonicity
#assert_no_axioms FX1Poly.Axis.fxMode_hasModeRelativeConvDecision
#assert_no_axioms FX1Poly.Axis.fxMode_hasSaturatedModeRelativeConvDecisionAtAdjunction

-- The r7 TERMINAL link: master flag `false` ↔ deep-wall reconciliation marker `true`
#assert_no_axioms FX1Poly.Axis.modeRelativeConvDecision_isDeepWall_notDischargeable

end FX1PolyAudit
