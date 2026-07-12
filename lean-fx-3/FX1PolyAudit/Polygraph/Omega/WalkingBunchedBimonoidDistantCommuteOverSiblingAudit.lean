import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidDistantCommuteOverSibling

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidDistantCommuteOverSiblingAudit — zero-axiom gate for the
r17 decisive distant-commute wall instance closed over the U1 sibling (WP-PROP r20, U2).

Per-declaration `#assert_no_axioms` on the two edge-letter reshapes, the flagship distant-commute atom `(4, 0, 2)`
over the sibling, the matrix-share pin, and every marker, PLUS an independent (non-fuel) `#print axioms` on the
load-bearing declarations and every marker.  The project `#assert_no_axioms` macro is fuel-based; the independent
`#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- U2.A — the two edge-letter reshapes (the U1 unitor spent on the `a^0 = id point` pads).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtLeadingPairReshapeConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtTrailingPairReshapeConv

-- U2.B — the flagship atom over the sibling + the matrix-share pin.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapCommuteFourZeroTwoMatrixShared

-- The markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteAtomOverSiblingShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericPositionStillWalled

-- Independent (non-fuel) axiom prints — the load-bearing declarations and every marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtLeadingPairReshapeConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtTrailingPairReshapeConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapCommuteFourZeroTwoOverSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantSwapCommuteFourZeroTwoMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteAtomOverSiblingShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteGenericPositionStillWalled

end FX1PolyAudit
