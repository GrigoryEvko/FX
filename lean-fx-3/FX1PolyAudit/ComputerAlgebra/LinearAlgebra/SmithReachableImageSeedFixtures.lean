import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithReachableImageSeedFixtures

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithReachableImageSeedFixtures — zero-axiom gate
    (H2-SMITH r34, #2261 — the corrected-route round)

Per-declaration zero-axiom gate for: the advanced-matrix helpers (`matrixAdvancedByPivotZeroSweep`,
`landedMagnitudeAt`, `minorGcdMagnitudeAt`); the two structural fill-in pins
(`advancedMatrixCarriesInteriorFillIn…`); and the ten in-driver-image magnitude fixtures
`|landed@1| = gcd(minor@1)` on the NON-diagonal advanced matrices the repair phase threads.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The advanced-matrix helpers. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixAdvancedByPivotZeroSweep
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeAt
#assert_no_axioms FX1Poly.ComputerAlgebra.minorGcdMagnitudeAt

/- The advanced matrix carries genuine interior fill-in (the NON-diagonal object). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.advancedMatrixCarriesInteriorFillInReplumb
#assert_no_axioms FX1Poly.ComputerAlgebra.advancedMatrixCarriesInteriorFillInThree

/- The seed's magnitude body TRUE on the advanced matrices. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedSixTenEight
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedTwelveEighteenThirty
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedThirtyTwentyTwelve
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNineSixFour
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNegativeTwelveEighteenThirty
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedCoprimeThreeFiveSeven
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedReplumbFifteenTenSixFour
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedTwelveEighteenThirtyFortyTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNonSquareThreeByTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNonSquareTwoByFour

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.matrixAdvancedByPivotZeroSweep
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeAt
#print axioms FX1Poly.ComputerAlgebra.minorGcdMagnitudeAt
#print axioms FX1Poly.ComputerAlgebra.advancedMatrixCarriesInteriorFillInReplumb
#print axioms FX1Poly.ComputerAlgebra.advancedMatrixCarriesInteriorFillInThree
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedSixTenEight
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedTwelveEighteenThirty
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedThirtyTwentyTwelve
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNineSixFour
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNegativeTwelveEighteenThirty
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedCoprimeThreeFiveSeven
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedReplumbFifteenTenSixFour
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedTwelveEighteenThirtyFortyTwo
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNonSquareThreeByTwo
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnAdvancedNonSquareTwoByFour

end FX1PolyAudit
