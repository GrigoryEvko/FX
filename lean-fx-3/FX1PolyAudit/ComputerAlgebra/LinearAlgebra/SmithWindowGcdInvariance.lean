import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowGcdInvariance

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithWindowGcdInvariance — zero-axiom gate
    (H2-SMITH r25, #2261 — the gcd-ideal CONVERSE brick + its truth-probes)

Per-declaration zero-axiom gate for `commonDivisorOfInputMinorDividesLandedPivot` (every common divisor
of the input minor divides the landed pivot) and its five kernel-checked truth-probes (exit-scan
hostile / dividing, scalar gcd-invariance rotation, common-divisor-divides-landed-pivot on a
non-coprime diagonal window AND a hostile non-diagonal seed, the escaping interior off-diagonal cell).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The truth-probes (kernel-checked concrete instances). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithExitScanDoesNotExitOnCoprimeDiagonalWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithExitScanExitsOnDividingDiagonalWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdInvariantOnConcreteEuclidRotation
#assert_no_axioms FX1Poly.ComputerAlgebra.commonDivisorTwoDividesLandedPivotOnNonCoprimeDiagonalWindow
#assert_no_axioms FX1Poly.ComputerAlgebra.commonDivisorTwoDividesLandedPivotOnHostileNonDiagonalSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSweepLeavesInteriorNonzeroOnCoprimeWindow

/- The brick — the gcd-ideal CONVERSE (forward-tower read-off at the diagonal slot). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.commonDivisorOfInputMinorDividesLandedPivot

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithExitScanDoesNotExitOnCoprimeDiagonalWindow
#print axioms FX1Poly.ComputerAlgebra.smithExitScanExitsOnDividingDiagonalWindow
#print axioms FX1Poly.ComputerAlgebra.intGcdInvariantOnConcreteEuclidRotation
#print axioms FX1Poly.ComputerAlgebra.commonDivisorTwoDividesLandedPivotOnNonCoprimeDiagonalWindow
#print axioms FX1Poly.ComputerAlgebra.commonDivisorTwoDividesLandedPivotOnHostileNonDiagonalSeed
#print axioms FX1Poly.ComputerAlgebra.smithSweepLeavesInteriorNonzeroOnCoprimeWindow
#print axioms FX1Poly.ComputerAlgebra.commonDivisorOfInputMinorDividesLandedPivot

end FX1PolyAudit
