import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntOrderAlgebra — zero-axiom gate
    (FLOAT-1 brick 8)

Per-declaration zero-axiom gate for the order/algebra interaction: the sign-case `≤`
builders, totality, add-monotonicity, and multiplication positivity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

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

end FX1PolyAudit
