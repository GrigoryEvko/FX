import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.ReverseCompletenessLeg

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ReverseCompletenessLeg — zero-axiom gate for the reverse-
completeness leg driven by the per-component decider (WP-AMALG-2 r3, B3)

Per-declaration zero-axiom gate: the router, the proof extractor, the three fire/decline verdicts, the
decider-driven convertibility, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the router + the proof extractor (the leg)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageConvOfDecided

-- the leg fires / declines (non-vacuity) + the decider-driven conv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesConv_assoc
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesConv_leftUnit
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesConv_faces
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutAssocRightImagesConvViaDecider

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRightImageReverseCompleteness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_fullReverseCompletenessStaysWalled

end FX1PolyAudit
