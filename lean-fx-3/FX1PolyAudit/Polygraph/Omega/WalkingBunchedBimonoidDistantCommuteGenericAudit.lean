import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidDistantCommuteGeneric

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidDistantCommuteGenericAudit — zero-axiom gate for the
FULLY GENERIC distant-commute (`sigmaAt w i ; sigmaAt w j ~ sigmaAt w j ; sigmaAt w i`, `j >= i + 2`) as ONE
Godement interchange fire under a left pad, over the SHIPPED star scope (WP-PROP r21, G1+G2).

Per-declaration `#assert_no_axioms` on the reusable dim-1 word fold (Brick A), the two padded-letter reshapes
(Bricks B, C), the two functorial folds (Brick D), the generic distant-commute theorem, its sibling wrapper, the
four concrete `sigmaAt`-form instances, the three matrix-share pins, and every marker — PLUS an independent
(non-fuel) `#print axioms` on the load-bearing declarations and every marker.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- Brick A — the reusable dim-1 word triple fold.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWordTripleFoldConv

-- Bricks B, C — the two padded-letter reshapes.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantFirstLetterReshapeConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSecondLetterReshapeConv

-- Brick D — the two functorial folds.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantLhsFoldConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantRhsFoldConv

-- G2 — the generic distant-commute + the sibling wrapper.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteGenericLetterConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteGenericLetterConvOverSibling

-- G2.B — the concrete sigmaAt-form instances + matrix-share pins.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtFiveZeroTwoOverSibling
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtFiveZeroThreeOverSibling
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtFiveOneThreeOverSibling
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtSixOneFourOverSibling
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteFiveZeroTwoMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteFiveOneThreeMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSixOneFourMatrixShared

-- The markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericAdditiveShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericSigmaAtInstancesShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericBraidAndPermWordLiftStillOpen

-- Independent (non-fuel) axiom prints — the load-bearing declarations and every marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWordTripleFoldConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantFirstLetterReshapeConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSecondLetterReshapeConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantLhsFoldConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantRhsFoldConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteGenericLetterConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteGenericLetterConvOverSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtFiveZeroTwoOverSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtFiveZeroThreeOverSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtFiveOneThreeOverSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSigmaAtSixOneFourOverSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteFiveZeroTwoMatrixShared
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteFiveOneThreeMatrixShared
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteSixOneFourMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericAdditiveShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericSigmaAtInstancesShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericBraidAndPermWordLiftStillOpen

end FX1PolyAudit
