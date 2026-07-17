import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RealOrderMonotoneMultiply

/-! # FX1PolyAudit/ComputerAlgebra/Number/RealOrderMonotoneMultiply — zero-axiom
    gate (NUM-R-5d monotone multiplication)

Per-declaration zero-axiom gate for ℝ-order monotone multiplication: the
pointwise multiplicative crux (`mulRealVanishingLowerBoundLeftNonNeg`), the
one-sided monotone laws (`realMulLeftMonotone`, `realMulRightMonotone`), the
two-sided `realMulMonotone`, and the capability marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealVanishingLowerBoundLeftNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.realMulLeftMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.realMulRightMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.realMulMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.fxRegularReal_hasOrderMonotoneMultiply

end FX1PolyAudit
