import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRiffleAssembly

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidRiffleAssemblyAudit — zero-axiom gate for the general
`wideSwap(m,n)` riffle word (the r7 wall falls), the staged bialgebra NF matched to the collision, the Coxeter
sorted-NF scaffold, and the honest star partial (WP-PROP r8, #2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms`
on the three recursive riffle defs (`blockPastBlock`/`riffleIn`/`wideSwap` — the structural-recursion witnesses),
the flagship `wideSwap 2 2 = middleSwap` matrix theorem, and the staged-NF-matches-collision probe.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- B1 — the three-layer riffle word (the general wideSwap, the r7 wall falls).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockPastBlock
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRiffleIn
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockPastBlockTwoTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRiffleInTwoOneIsMiddleSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapOneOneMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoOneIsIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapOneTwoIsIdentity
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoTwoIsMiddleSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapThreeTwoMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideSwapGeneralRiffleWordShipped

-- Independent (non-fuel) axiom prints on the three recursive riffle defs + the flagship matrix theorem.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBlockPastBlock
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRiffleIn
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwap
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidWideSwapTwoTwoIsMiddleSwap

-- B2 — the staged bialgebra NF + the collision matrix side (matrix-correct at generic width).
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaStage
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuStage
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNF
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNFMatchesCollisionTwoTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNFMatchesCollisionTwoThree
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNFMatchesCollisionThreeTwo
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNFMatchesCollisionThreeThree
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_stagedNormalFormMatrixSideShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_wideCollisionConvGatedOnGenericNaturality

-- Independent (non-fuel) axiom prints on the two staged recursive defs + the flagship generic-width NF match.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaStage
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMuStage
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBialgebraNFMatchesCollisionTwoThree

-- B3 — the Coxeter sorted-NF scaffold: the carrier + the fuel-structural sort.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAt
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtThreeZeroIsFirstTransposition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidSigmaAtThreeOneIsSecondTransposition
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWord
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordBraidLeftMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordBraidRightMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidYangBaxterLeftLegMatrix
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordBraidMatrixShared
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWordBraidMatchesYangBaxterLeft
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidInversionFuelBound
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBubbleSortOnePass
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBubbleSortFuel
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_coxeterSortNfScaffoldShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_coxeterWordUniqueGatedOnGenericBraid

-- Independent (non-fuel) axiom prints on the fuel-structural sort defs (no WellFounded.fix leak) + the carrier.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBubbleSortOnePass
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBubbleSortFuel
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPermWord

-- B4 — the star honest partial (markers only, NO star flip).
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starLegsGatedOnGenericNaturalityAndCoxeter
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRiffle
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_riffleAssemblyRoundEightLedgerShipped

-- Independent (non-fuel) axiom prints on the B4 narrowing marker + the no-flip marker + the round ledger.
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starLegsGatedOnGenericNaturalityAndCoxeter
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterRiffle
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_riffleAssemblyRoundEightLedgerShipped

end FX1PolyAudit
