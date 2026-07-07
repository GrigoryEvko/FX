import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FixedWidth.OverflowArithmetic

/-! # FX1PolyAudit/ComputerAlgebra/FixedWidth/OverflowArithmetic — zero-axiom gate

Per-declaration zero-axiom gate for the wrap / trap / saturate arithmetic: the
order-to-`Bool` bridges, the wrap aliases + modular characterisations, the trap
`Option` ops with their fits/overflow/exact/agrees-wrap semantics, and the
saturate ops with in-range / clamp / upper-bound semantics.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natBltEqTrueOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.natBleEqFalseOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.natBltEqFalseOfLe
#assert_no_axioms FX1Poly.ComputerAlgebra.wrapAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.wrapMul
#assert_no_axioms FX1Poly.ComputerAlgebra.wrapAddIsModularSum
#assert_no_axioms FX1Poly.ComputerAlgebra.wrapMulIsModularProduct
#assert_no_axioms FX1Poly.ComputerAlgebra.trapAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.trapMul
#assert_no_axioms FX1Poly.ComputerAlgebra.trapAddFits
#assert_no_axioms FX1Poly.ComputerAlgebra.trapAddOverflows
#assert_no_axioms FX1Poly.ComputerAlgebra.trapAddSomeIsExact
#assert_no_axioms FX1Poly.ComputerAlgebra.trapAddSomeAgreesWrap
#assert_no_axioms FX1Poly.ComputerAlgebra.trapMulFits
#assert_no_axioms FX1Poly.ComputerAlgebra.trapMulOverflows
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMaxUnsigned
#assert_no_axioms FX1Poly.ComputerAlgebra.maxUnsignedBelowModulus
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMaxUnsignedToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.saturateAddUnsigned
#assert_no_axioms FX1Poly.ComputerAlgebra.saturateMulUnsigned
#assert_no_axioms FX1Poly.ComputerAlgebra.saturateAddInRange
#assert_no_axioms FX1Poly.ComputerAlgebra.saturateAddClamps
#assert_no_axioms FX1Poly.ComputerAlgebra.natLeSubOneOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.saturateAddUpperBounded

end FX1PolyAudit
