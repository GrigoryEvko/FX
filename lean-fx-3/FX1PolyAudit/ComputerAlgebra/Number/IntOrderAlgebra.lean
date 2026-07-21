import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # Zero-axiom gate for `IntOrderAlgebra`

Per-declaration zero-axiom gate for the order/algebra interaction: the sign-case `≤`
builders, totality, add-monotonicity, and multiplication positivity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatLeOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSuccLeOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSuccLeNegSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.intZeroLeOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intZeroLeDest
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessEqualOfLessThan
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddLeAddLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddLeAddRight
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulPos
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanOfEqLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanOfEqRight
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanAddOne
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanOfLessEqualOfLessThan
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanOfLessThanOfLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddLessThanAddLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddLessThanAddRight
#assert_no_axioms FX1Poly.ComputerAlgebra.intSelfLessEqualOfNatNatAbs
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegSelfLessEqualOfNatNatAbs
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanOfNatNatAbsSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanIrrefl
#assert_no_axioms FX1Poly.ComputerAlgebra.intLessThanOfNotLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.intAddLeftCancelLessEqual

end FX1PolyAudit
