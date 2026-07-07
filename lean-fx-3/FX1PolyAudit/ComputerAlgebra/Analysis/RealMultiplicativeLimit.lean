import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealMultiplicativeLimit

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealMultiplicativeLimit — zero-axiom
    gate (ANALYSIS-MULLIMIT-1)

Per-declaration zero-axiom gate for the real multiplicative limit laws: the
additive-monoid reshaping shims, the uniform magnitude bound of a convergent
sequence (tail + structural prefix sum), the real-level product-difference law
(the deferred analytic core), and the product and scalar limit laws.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactSwapOuterIntoInner
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactGatherDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.convergentTailIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.sumOverPrefix
#assert_no_axioms FX1Poly.ComputerAlgebra.natMemberLeSumOverPrefix
#assert_no_axioms FX1Poly.ComputerAlgebra.convergentSequenceIsBounded
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealRespectsIsWithinRealBound
#assert_no_axioms FX1Poly.ComputerAlgebra.canonicalBoundNumeratorPredecessor
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToMulReal
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToScalarMulReal

end FX1PolyAudit
