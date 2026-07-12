import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRunBelowCommuteConv

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRunBelowCommuteConvAudit — zero-axiom gate for the
`Below` twin of the first Cartier–Foata fold rung (WP-PROP r23, F1).

Per-declaration `#assert_no_axioms` on the `Below` fold rung `swapCommutesRunBelowConv`, its width-4 non-vacuity
instance, the `[2,0]`/`[0,2]` matrix-share pin, and both markers — PLUS an independent (non-fuel) `#print axioms`
on the same declarations.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms`
closes the gate. -/

namespace FX1PolyAudit

-- F1 — the Below CONV fold rung.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapCommutesRunBelowConv

-- The non-vacuity instance + the matrix-share pin.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRunBelowCommuteConvWidthFourInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRunBelowCommuteTwoZeroMatrixShared

-- The markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_swapCommutesRunBelowConvShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combFoldsBraidWalledDownstreamOfCarry

-- Independent (non-fuel) axiom prints.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSwapCommutesRunBelowConv
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRunBelowCommuteConvWidthFourInstance
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRunBelowCommuteTwoZeroMatrixShared
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_swapCommutesRunBelowConvShipped
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_combFoldsBraidWalledDownstreamOfCarry

end FX1PolyAudit
