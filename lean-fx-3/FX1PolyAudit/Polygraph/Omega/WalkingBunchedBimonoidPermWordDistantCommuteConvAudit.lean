import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermWordDistantCommuteConv

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidPermWordDistantCommuteConvAudit — zero-axiom gate for
the `permWord`-level distant-commute and the first Cartier–Foata fold rung (WP-PROP r22, P1+P2+P3).

Per-declaration `#assert_no_axioms` on the right-tail id bridge (P1a), the `sigmaAt` trailing-id absorber (P1b),
the `sigmaAt`-form generic distant-commute (P2 atom), the two-letter `permWord` lift (P2), the first fold rung
`swapCommutesRunAboveConv` (P3), the width-4 matrix-share pin, and every marker — PLUS an independent
(non-fuel) `#print axioms` on the load-bearing declarations and every marker.  The project `#assert_no_axioms`
macro is fuel-based; the independent `#print axioms` closes the gate.  (The private A1 / A2 truncated-subtraction
arithmetic is covered transitively — its cleanliness shows in the public theorems' axiom sets.) -/

namespace FX1PolyAudit

-- P1 — the right-tail id bridge + the sigmaAt trailing-id absorber.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidVcompIdRightBridgedWithId
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtTrailingIdAbsorbConv

-- P2 — the sigmaAt-form generic distant-commute + the two-letter permWord lift.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtDistantCommuteConv
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordTwoLetterDistantCommuteConv

-- P3 — the first CONV fold rung.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapCommutesRunAboveConv

-- The matrix-share pin.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordDistantCommuteFourZeroTwoMatrixShared

-- The markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_sigmaAtTrailingBoundaryReshapeShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_sigmaAtGenericDistantCommuteConvShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_swapCommutesRunAboveConvShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_swapCommutesRunBelowAndCombFoldsStillOpen

-- Independent (non-fuel) axiom prints — the load-bearing declarations and every marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidVcompIdRightBridgedWithId
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtTrailingIdAbsorbConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtDistantCommuteConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordTwoLetterDistantCommuteConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapCommutesRunAboveConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordDistantCommuteFourZeroTwoMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_sigmaAtTrailingBoundaryReshapeShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_sigmaAtGenericDistantCommuteConvShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_swapCommutesRunAboveConvShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_swapCommutesRunBelowAndCombFoldsStillOpen

end FX1PolyAudit
