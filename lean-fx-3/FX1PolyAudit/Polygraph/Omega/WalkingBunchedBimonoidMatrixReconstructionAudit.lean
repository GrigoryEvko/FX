import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixReconstruction

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidMatrixReconstructionAudit — zero-axiom gate for the
matrix reconstruction kit + the two Node-A residuals (WP-PROP r5, #2033).

Per-declaration `#assert_no_axioms` on: the reconstruction kit (range-succ-cons, list rebuilds, matrix
reconstruction, the get-of-range-map readers, the matMul entry read); the finite-sum Fubini kit
(middle-four, add/mul/mul distributivity + associativity, zero-mul, sum-mul-left/right, sum-map-add,
sum-of-zeros, range-sum-successor, the Fubini swap); Node A residual (1) general `matMul` associativity + probe;
Node A residual (2) the `decide`-based delta helpers, the identity matrix entry, both delta collapses, both
identity unit laws + probe; and the B1-kit / Node-A markers.

Independent `#print axioms` (NOT fuel-based, MEMORY: mandatory) on the reconstruction, the Fubini swap, the
general associativity, and both unit laws closes the gate. -/

namespace FX1PolyAudit

-- The reconstruction kit.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRangeSuccCons
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListRebuild
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListRebuild
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListGetRangeMap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRowListGetRangeMap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatReconstruct
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulEntryRead

-- The finite-sum Fubini kit.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMiddleFour
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAddMul
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMulAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMulAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatZeroMul
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSumMulRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSumMulLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSumMapAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListSumMapZero
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSumRangeSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListSumSwap

-- Node A residual (1) — general matMul associativity.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulAssocProbeNonSquare

-- Node A residual (2) — the delta helpers + identity entry + collapses + unit laws.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDecideEqTrue
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDecideEqFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatMulOne
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatOneMul
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaMulRightEq
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaMulRightNe
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaMulLeftEq
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaMulLeftNe
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityMatEntry
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaCollapseRight
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaCollapseLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityRightUnit
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityLeftUnit

-- The truth-probes + the markers.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatReconstructProbeTwoThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulEntryReadProbe
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityRightUnitProbe
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_reconstructionAndFubiniKitShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAMatMulAssocShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAIdentityUnitsShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_nodeAMatMulLawsCompleteBiDividend

-- Independent (non-fuel) axiom prints on the load-bearing theorems.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatReconstruct
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidNatListSumSwap
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMatMulAssoc
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityRightUnit
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityLeftUnit

end FX1PolyAudit
