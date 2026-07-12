import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRunCommuteConvOverSibling

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRunCommuteConvOverSiblingAudit — zero-axiom gate for the
first CONV run-commute lemma over the U1 sibling + the honest star-chain census after U3 (WP-PROP r20, U3).

Per-declaration `#assert_no_axioms` on the run-head run-commute lemma, its matrix-share pin, and every marker,
PLUS an independent (non-fuel) `#print axioms` on the load-bearing declarations and every marker.  The project
`#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- U3.A — the first run-commute-CONV lemma over the sibling + the matrix-share pin.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteRunHeadConvOverSibling
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteRunHeadMatrixShared

-- U3.B — the r17-marker literal delivery + the star-chain census markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteRunConvOverSiblingShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_shippedScopeRunCommuteStillGatedNoFlip
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starChainCensusAfterUThreeStillOpen

-- Independent (non-fuel) axiom prints — the load-bearing declarations and every marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteRunHeadConvOverSibling
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDistantCommuteRunHeadMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_distantCommuteRunConvOverSiblingShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_shippedScopeRunCommuteStillGatedNoFlip
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starChainCensusAfterUThreeStillOpen

end FX1PolyAudit
