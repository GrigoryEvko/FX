import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCanonicalDriverInterface

/-! # FX1PolyAudit.ComputerAlgebra.LinearAlgebra.SmithCanonicalDriverInterfaceAxiomWitness —
    independent #print axioms (H2-SMITH r51)

An INDEPENDENT `#print axioms` cross-check — a separate mechanism in a separate file from the
fuel-based `#assert_no_axioms` gate of the per-file twin — over every declaration of the driver-agnostic
Smith interface: the canonical driver, its totality target and theorem, the driver-agnostic reachability
statement and theorem, the seven liveness probes and their rectangularity witnesses, the seven
mandate-application pins, and the seven driver-agnostic existence pins.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.ComputerAlgebra.smithReduceCanonical
#print axioms FX1Poly.ComputerAlgebra.SmithReduceCanonicalDriverStatement
#print axioms FX1Poly.ComputerAlgebra.smithReduceCanonicalDriverHolds
#print axioms FX1Poly.ComputerAlgebra.SmithNormalFormIsReachableStatement
#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachable

#print axioms FX1Poly.ComputerAlgebra.canonicalProbeDensePair
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeDiagonalNine
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeWideRun
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeTallCoprime
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeAntidiagonal
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeTripleDiagonal
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeNegativeMix

#print axioms FX1Poly.ComputerAlgebra.canonicalProbeDensePairIsRectangular
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeDiagonalNineIsRectangular
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeWideRunIsRectangular
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeTallCoprimeIsRectangular
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeAntidiagonalIsRectangular
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeTripleDiagonalIsRectangular
#print axioms FX1Poly.ComputerAlgebra.canonicalProbeNegativeMixIsRectangular

#print axioms FX1Poly.ComputerAlgebra.canonicalDriverLandsSmithFormOnDensePair
#print axioms FX1Poly.ComputerAlgebra.canonicalDriverLandsSmithFormOnDiagonalNine
#print axioms FX1Poly.ComputerAlgebra.canonicalDriverLandsSmithFormOnWideRun
#print axioms FX1Poly.ComputerAlgebra.canonicalDriverLandsSmithFormOnTallCoprime
#print axioms FX1Poly.ComputerAlgebra.canonicalDriverLandsSmithFormOnAntidiagonal
#print axioms FX1Poly.ComputerAlgebra.canonicalDriverLandsSmithFormOnTripleDiagonal
#print axioms FX1Poly.ComputerAlgebra.canonicalDriverLandsSmithFormOnNegativeMix

#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachableForDensePair
#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachableForDiagonalNine
#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachableForWideRun
#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachableForTallCoprime
#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachableForAntidiagonal
#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachableForTripleDiagonal
#print axioms FX1Poly.ComputerAlgebra.smithNormalFormIsReachableForNegativeMix

end FX1PolyAudit
