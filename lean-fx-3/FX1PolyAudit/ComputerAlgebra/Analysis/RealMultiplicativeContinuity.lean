import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealMultiplicativeContinuity

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealMultiplicativeContinuity —
    zero-axiom gate (ANALYSIS-MULCONT-1)

Per-declaration zero-axiom gate for real multiplicative continuity: the
fixed-factor scale collapse and zero-leg drop shims, bounded-domain two-variable
multiplication continuity, and global fixed-factor continuity with its uniform
continuity packaging.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.factorScaledIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.factorReciprocalScaledCollapses
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mulExactZeroRightDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealIsWithinRealBoundOnBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarMulRealIsWithinRealBound
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarMulRealIsUniformlyContinuous
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarMulRealExactBoundOfReal
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealByFixedRealIsUniformlyContinuous
#assert_no_axioms FX1Poly.ComputerAlgebra.isUniformlyContinuousScalarMulFunction

end FX1PolyAudit
