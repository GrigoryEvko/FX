import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithLandedMagnitudeRefuted

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithLandedMagnitudeRefuted — zero-axiom gate
    (H2-SMITH r33, #2261 — the general per-phase keystone and the corrected-driver seed are FALSE)

Per-declaration zero-axiom gate for the r33 refutation of the general keystone
`SmithCascadeLandedPivotDividesMinor`, the magnitude identity `MinAbsEuclidLandsMinorGcdMagnitude`, and
the corrected-driver's sole hypothesis `SmithCascadeLandsDivisibleSubBlock`
(`smithCascadeLandsDivisibleSubBlockIsRefuted`, the load-bearing negative theorem), together with the
seed rectangularity, the seed magnitude mismatch, the hostile robustness battery, and the diagonal
restricted-form contrast.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

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

-- Independent (non-fuel) axiom prints on every declaration.
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
