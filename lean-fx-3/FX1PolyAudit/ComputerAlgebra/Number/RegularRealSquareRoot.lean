import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealSquareRoot

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealSquareRoot — zero-axiom gate
    (NUM-R-SQRT #1961)

Per-declaration zero-axiom gate for constructive square root: the integer square root
by counting and its two-sided certificate, plus the strict-monotone-square micro-lemmas.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natLtTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.natSquareStrictMonoSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.natSqrtStep
#assert_no_axioms FX1Poly.ComputerAlgebra.natSqrt
#assert_no_axioms FX1Poly.ComputerAlgebra.natSqrtBounds
#assert_no_axioms FX1Poly.ComputerAlgebra.natSqrtLowerBound
#assert_no_axioms FX1Poly.ComputerAlgebra.natSqrtUpperBound
#assert_no_axioms FX1Poly.ComputerAlgebra.natMulLeMulRight
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalSqrtRadicand
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalSqrtApprox
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalSqrtApproxSqLe
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalSqrtApproxSuccSqGe
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtSampleIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtGridIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtSampleIndexSuccessor
#assert_no_axioms FX1Poly.ComputerAlgebra.natSelfLeSqrtSampleIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.sqrtRealApproximation

end FX1PolyAudit
