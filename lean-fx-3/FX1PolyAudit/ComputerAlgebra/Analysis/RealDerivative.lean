import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Analysis.RealDerivative

/-! # FX1PolyAudit/ComputerAlgebra/Analysis/RealDerivative — zero-axiom gate

Per-declaration zero-axiom gate for the real derivative layer: the real-level
distance congruences and convergence-transport lemmas, the ring reshaping
shims, the difference quotient and `HasDerivativeAt` predicate, the
constant/identity/linearity/scalar rules, differentiable-implies-continuous,
and the product (Leibniz) rule.

Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundCongrLeftDenotesSameReal
#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundCongrRightDenotesSameReal
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToOfPointwiseDenotesSameReal
#assert_no_axioms FX1Poly.ComputerAlgebra.convergesToCongrLimitDenotesSameReal
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealNegLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.subRealAddPerturbationDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealSubRealBaseDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealSubRealTelescopeDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.subRealMulTelescopeDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.differenceQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.HasDerivativeAt
#assert_no_axioms FX1Poly.ComputerAlgebra.hasDerivativeAtConstant
#assert_no_axioms FX1Poly.ComputerAlgebra.hasDerivativeAtIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.hasDerivativeAtAddReal
#assert_no_axioms FX1Poly.ComputerAlgebra.hasDerivativeAtScalarMulReal
#assert_no_axioms FX1Poly.ComputerAlgebra.differentiableImpliesContinuous
#assert_no_axioms FX1Poly.ComputerAlgebra.productDifferenceQuotientDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.hasDerivativeAtMulReal

end FX1PolyAudit
