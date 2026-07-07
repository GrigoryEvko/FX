import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FixedWidth.Widening

/-! # FX1PolyAudit/ComputerAlgebra/FixedWidth/Widening — zero-axiom gate

Per-declaration zero-axiom gate for the value-preserving zero-extension widening
(and its `UIntN` view form) and the genuine `Nat ↠ BitVec (width+1)` number-tower
reduction semiring homomorphism plus its three reducer laws.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.valueBelowWiderModulus
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecZeroExtendWideningPreservesToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.zeroExtend
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNZeroExtendPreservesValue
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOfNatModAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOfNatModMul
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOfNatModZero
#assert_no_axioms FX1Poly.ComputerAlgebra.reduceNatToBitVec

end FX1PolyAudit
