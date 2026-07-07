import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Bits.BitVecRing

/-! # FX1PolyAudit/ComputerAlgebra/Bits/BitVecRing — zero-axiom gate

Per-declaration zero-axiom gate for `Z / 2^(width+1) Z` as a commutative ring:
the eight ring laws (add/mul commutativity and associativity, right additive
identity and inverse, right multiplicative identity, left distributivity), the
unit read-back and nontriviality, and the packaged `CommutativeRingWitness`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMulComm
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAddZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecAddNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMulDistribLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecOneToNat
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecMulOneRight
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecZeroApartOne
#assert_no_axioms FX1Poly.ComputerAlgebra.bitVecCommutativeRingWitness

end FX1PolyAudit
