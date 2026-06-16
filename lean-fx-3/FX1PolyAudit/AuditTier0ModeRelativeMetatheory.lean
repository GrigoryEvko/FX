import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.ModeRelativeMetatheory

/-! # FX1PolyAudit/AuditTier0ModeRelativeMetatheory — zero-axiom gate for mode-9

Per-declaration zero-axiom gate for `mode-9` (`FX1Poly/Tier0/Mode/ModeRelativeMetatheory.lean`): the
computad→ωcE word encoding (the dimension-1 bridge) + its monoid homomorphism / length / distinguisher, the
faithful-tagging dimension-1 word-problem DECISION (reusing the ωcE word `DecidableEq` via `decidable_of_iff`),
the concrete adjunction tagging, the trivial-mode canonicity base, the mode-relative parameter, and the markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The computad → ωcE word encoding (the dimension-1 bridge)
#assert_no_axioms FX1Poly.Tier0.ComputadGeneratorTagging
#assert_no_axioms FX1Poly.Tier0.ModalityPath.encodeSlots
#assert_no_axioms FX1Poly.Tier0.ModalityPath.encodeWordCode
#assert_no_axioms FX1Poly.Tier0.ModalityPath.encodeSlots_composePath
#assert_no_axioms FX1Poly.Tier0.ModalityPath.encodeWordCode_composePath
#assert_no_axioms FX1Poly.Tier0.ModalityPath.encodeWordCode_identityPath
#assert_no_axioms FX1Poly.Tier0.ModalityPath.encodeWordCode_length
#assert_no_axioms FX1Poly.Tier0.ModalityPath.ne_of_encodeWordCode_ne

-- The dimension-1 word problem DECIDED (reusing the ωcE word DecidableEq)
#assert_no_axioms FX1Poly.Tier0.FaithfulComputadTagging
#assert_no_axioms FX1Poly.Tier0.FaithfulComputadTagging.decidableOneCellEq

-- The concrete adjunction tagging + the computed encoding
#assert_no_axioms FX1Poly.Tier0.adjunctionTagging
#assert_no_axioms FX1Poly.Tier0.adjunctionLeftThenRight_encodeWordCode

-- Multimodal canonicity (the trivial-mode base) + the mode-relative parameter
#assert_no_axioms FX1Poly.Tier0.trivialComputad_oneCell_length_zero
#assert_no_axioms FX1Poly.Tier0.Computad.modeRelativeParameter

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMultimodalCanonicity
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeRelativeConvDecision

end FX1PolyAudit
