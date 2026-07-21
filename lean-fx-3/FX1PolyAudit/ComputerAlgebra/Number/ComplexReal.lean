import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexReal

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexReal — zero-axiom gate

Per-declaration zero-axiom gate for the Gaussian reals: the carrier, the
product setoid with refl/symm/trans, the operations and constants, every
operation congruence, the three conjugation laws, the commutative-ring laws, and
the ℝ and ℂ commutative-ring certificates.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ComplexReal
#assert_no_axioms FX1Poly.ComputerAlgebra.DenotesSameComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameComplexRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameComplexSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameComplexTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.negComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.subComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.conjComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.zeroComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.oneComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.imaginaryUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.negComplexRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.subComplexRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.conjComplexRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.conjComplexInvolutive
#assert_no_axioms FX1Poly.ComputerAlgebra.conjComplexAddComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.conjComplexMulComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexComm
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexComm
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexOneRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexLeftDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.regularRealZeroIsApartFromOne
#assert_no_axioms FX1Poly.ComputerAlgebra.regularRealCommutativeRingWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.complexRealZeroIsApartFromOne
#assert_no_axioms FX1Poly.ComputerAlgebra.complexCommutativeRingWitness

end FX1PolyAudit
