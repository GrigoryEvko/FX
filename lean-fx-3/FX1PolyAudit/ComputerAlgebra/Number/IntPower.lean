import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntPower

/-! # Zero-axiom gate for `IntPower`

Per-declaration zero-axiom gate for the Nat-power of an Int and its alignment/positivity
algebra. Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intPower
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerPos
#assert_no_axioms FX1Poly.ComputerAlgebra.intOnePower
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulPowerFold

end FX1PolyAudit
