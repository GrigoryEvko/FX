import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntCancellation

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntCancellation — zero-axiom gate
    (FLOAT-2 brick 3)

Per-declaration zero-axiom gate for the multiplicative cancellation kit: the Nat
right-summand vanishing twin, the zero-product law at a positive successor carrier, and
the right/left/power cancellation laws.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natAddEqZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.intEqZeroOfMulOfNatSuccEqZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulRightCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulLeftCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulPowerRightCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulLeMulRightOfNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intLeOfMulLeMulRightOfPos
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegLeNegOfLe
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegLtNegOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulLeMulLeftOfNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulLeMulOfMagnitudeLe

end FX1PolyAudit
