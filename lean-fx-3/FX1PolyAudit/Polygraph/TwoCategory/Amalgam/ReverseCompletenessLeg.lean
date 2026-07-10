import FX1PolyAudit.DependencyAudit
import FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadBespokeFreeWalk
import FX1Poly.Polygraph.TwoCategory.Amalgam.ReverseCompletenessLeg

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ReverseCompletenessLeg — zero-axiom gate for the reverse-
completeness leg driven by the per-component decider (WP-AMALG-2 r3, B3; re-founded bespoke-free at B5)

Per-declaration zero-axiom gate: the router, the proof extractor, the three fire/decline verdicts, the
decider-driven convertibility, and the honesty markers.  PLUS the constant-closure META-WALK certifying the B5
re-founding: the LIVE router now has NO bespoke `monadSaturatedTwoCellDecision` in its full transitive closure.

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

/-! ## B5 re-founding: the LIVE router is now bespoke-free of `monadSaturatedTwoCellDecision` (constant-closure walk) -/

#assert_constant_free_of FX1Poly.Polygraph.Amalgam.pushoutRightImageDecidesConv
  needle FX1Poly.Polygraph.monadSaturatedTwoCellDecision
#assert_constant_free_of FX1Poly.Polygraph.Amalgam.pushoutRightImageConvOfDecided
  needle FX1Poly.Polygraph.monadSaturatedTwoCellDecision

end FX1PolyAudit
