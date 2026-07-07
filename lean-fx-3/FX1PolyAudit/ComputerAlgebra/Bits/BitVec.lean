import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Bits.BitVec

/-! # FX1PolyAudit/ComputerAlgebra/Bits/BitVec — zero-axiom gate

Per-declaration zero-axiom gate for the fixed-width machine-integer substrate:
the `mod 2^width` reducer, the constants, the modular arithmetic (add/neg/sub/
mul) with their `toNat` characterisations, decidable equality, the structural
per-bit access and bitwise logic (and/or/xor/not), the shifts (shl/shr/ashr),
concat/slice/zero-extend/sign-extend, and the unsigned/two's-complement
interpretations.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOfNatMod
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOfNatModToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecZero
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOne
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecZeroToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMul
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecSub
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAddToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMulToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecNegToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecDecidableEq
#assert_no_axioms FX1Poly.ComputerAlgebra.bitAtNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitWeight
#assert_no_axioms FX1Poly.ComputerAlgebra.bitwiseFold
#assert_no_axioms FX1Poly.ComputerAlgebra.bitwiseUnaryFold
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAnd
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOr
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecXor
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecNot
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecShl
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecShr
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecIsNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAshr
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecConcat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecExtract
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecZeroExtend
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecSignExtend
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecToInt

end FX1PolyAudit
