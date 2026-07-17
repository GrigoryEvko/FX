import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexPolynomial

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexPolynomial — zero-axiom gate

Per-declaration zero-axiom gate for the ℂ[x] evaluation foundation: the Horner evaluator, the four
coefficient-list operations (add / scale / negate / convolution-multiply), the derived ℂ ring identities
(the additive interchange, the additive-inverse uniqueness and its `negLeft` helper, the two zero-product
laws, right distributivity, negation of zero, negation over addition, negation through a factor), and the
four ring-homomorphism laws (`evalComplexPolyAdd` / `evalComplexPolyScale` / `evalComplexPolyNeg` /
`evalComplexPolyMul`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.evalComplexPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.scaleComplexPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.negComplexPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexInterchange
#assert_no_axioms FX1Poly.ComputerAlgebra.addComplexNegLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.negComplexUniqueOfAddZero
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexRightDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.negComplexZero
#assert_no_axioms FX1Poly.ComputerAlgebra.negComplexAddComplex
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.evalComplexPolyAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.evalComplexPolyScale
#assert_no_axioms FX1Poly.ComputerAlgebra.evalComplexPolyNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.evalComplexPolyMul
#assert_no_axioms FX1Poly.ComputerAlgebra.fxComplexReal_hasPolynomialEvaluation

end FX1PolyAudit
