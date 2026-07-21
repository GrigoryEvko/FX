import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithLandedMagnitudeRefuted

/-! # SmithLandedMagnitudeRefuted — zero-axiom gate

Per-declaration axiom audit for the refutation of the general keystone
`SmithCascadeLandedPivotDividesMinor`, the magnitude identity `MinAbsEuclidLandsMinorGcdMagnitude`, and the
driver's sole hypothesis `SmithCascadeLandsDivisibleSubBlock`, together with the seed facts, the
robustness battery, and the diagonal restricted-form contrast.  Each declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`; both the fuel-based
`#assert_no_axioms` and the independent `#print axioms` are run on every one. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.landedExceedsMinorGcdSeedIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.minAbsEuclidLandsMinorGcdMagnitudeIsRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeLandedPivotDividesMinorIsRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeLandsDivisibleSubBlockIsRefuted
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnCrossClearSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnNegativeSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnNonSquareSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnAntiDiagonalSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnDiagonalWindowContrast

#print axioms FX1Poly.ComputerAlgebra.landedExceedsMinorGcdSeedIsRectangular
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnSeed
#print axioms FX1Poly.ComputerAlgebra.minAbsEuclidLandsMinorGcdMagnitudeIsRefuted
#print axioms FX1Poly.ComputerAlgebra.smithCascadeLandedPivotDividesMinorIsRefuted
#print axioms FX1Poly.ComputerAlgebra.smithCascadeLandsDivisibleSubBlockIsRefuted
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnCrossClearSeed
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnNegativeSeed
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnNonSquareSeed
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeNeMinorGcdOnAntiDiagonalSeed
#print axioms FX1Poly.ComputerAlgebra.landedMagnitudeEqMinorGcdOnDiagonalWindowContrast

end FX1PolyAudit
