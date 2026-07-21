import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.IntNoZeroDivisors

/-! # Zero-axiom gate for `IntNoZeroDivisors`

Per-declaration zero-axiom gate for the arbitrary-sign ℤ no-zero-divisor law and
power-nonvanishing. The core `Int.mul_eq_zero` and `Int.natAbs_mul` both leak `propext`, so
the corpus routes through a hand-structural multiplicative `natAbs` and a
`Nat.noConfusion`-based Nat no-zero-divisor. Every declaration must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, and `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natMulEqZeroLeftFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.intNatAbsNegOfNat
#assert_no_axioms FX1Poly.ComputerAlgebra.intNatAbsMulByCases
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulEqZeroLeftFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intOneNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerNeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulNeZeroGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.intPowerNeZeroGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxInt_hasNoZeroDivisors

end FX1PolyAudit
