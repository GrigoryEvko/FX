import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntPower

/-! # FX1PolyAudit/ComputerAlgebra/Number/IntPower — zero-axiom gate (FLOAT-2 brick 1)

Per-declaration zero-axiom gate for the hand-rolled Nat-power of an Int and its
alignment/positivity algebra.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intPower
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerPos
#assert_no_axioms FX1Poly.ComputerAlgebra.intOnePower

end FX1PolyAudit
