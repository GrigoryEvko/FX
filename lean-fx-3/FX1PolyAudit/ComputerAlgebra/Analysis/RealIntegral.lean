import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealIntegral

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealIntegral — zero-axiom gate
    (ANALYSIS-INTEGRAL-1)

Per-declaration zero-axiom gate for the Riemann-sum functional layer: the
constant-real homomorphisms, the natural-scaling law, the rational mesh and
sample points, the cell-count/mesh telescope, the Riemann-sum functional, and
its exact linearity + constant laws.

Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.constantRealAddExact
#assert_no_axioms FX1Poly.ComputerAlgebra.constantRealMulExact
#assert_no_axioms FX1Poly.ComputerAlgebra.natRational
#assert_no_axioms FX1Poly.ComputerAlgebra.natRationalSuccDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.replicateRealEqScale
#assert_no_axioms FX1Poly.ComputerAlgebra.isMagnitudeWithinSelfOfNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.mulExactRespectsIsWithinBoundConstantLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.natRationalZeroDenotesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.natScaleRationalDenotesScale
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarMulRealExactBoundOfNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.meshWidth
#assert_no_axioms FX1Poly.ComputerAlgebra.samplePoint
#assert_no_axioms FX1Poly.ComputerAlgebra.cellCountMeshWidthDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.riemannSum
#assert_no_axioms FX1Poly.ComputerAlgebra.riemannSumAddReal
#assert_no_axioms FX1Poly.ComputerAlgebra.riemannSumScalarMulReal
#assert_no_axioms FX1Poly.ComputerAlgebra.riemannSumConstant

end FX1PolyAudit
