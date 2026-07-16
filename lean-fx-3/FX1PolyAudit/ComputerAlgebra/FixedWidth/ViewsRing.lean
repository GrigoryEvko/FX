import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.FixedWidth.ViewsRing

/-! # FX1PolyAudit/ComputerAlgebra/FixedWidth/ViewsRing — zero-axiom gate

Per-declaration zero-axiom gate for the `iN`/`uN` commutative-ring witnesses:
the unsigned two's-complement negation prerequisite, the sixteen transported
ring laws (add/mul commutativity and associativity, right additive identity and
inverse, left distributivity, right multiplicative identity) plus the two
nontriviality lemmas, and the two packaged `CommutativeRingWitness` objects.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.UIntN.neg

#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNMulComm
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNAddZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNAddNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNMulDistribLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNMulOneRight
#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNZeroApartOne

#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNAddComm
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNMulComm
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNAddAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNMulAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNAddZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNAddNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNMulDistribLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNMulOneRight
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNZeroApartOne

#assert_no_axioms FX1Poly.ComputerAlgebra.sIntNCommutativeRingWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.uIntNCommutativeRingWitness

end FX1PolyAudit
