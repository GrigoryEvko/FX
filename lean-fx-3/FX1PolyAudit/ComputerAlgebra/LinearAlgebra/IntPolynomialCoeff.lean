import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeff

/-! # FX1PolyAudit/.../IntPolynomialCoeff — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] positional coefficient accessor: the accessor, the four
coefficient ring homomorphisms (scale/add/neg/sub), the monomial-at-its-degree fact, and the monomial
coefficient shift.  Structural recursion on the list and position; corpus `Int` lemmas.  Free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffScale
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffSub
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffMonomialAt
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffSingletonZero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffMonomialMul
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffPastEnd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffScaleGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffMonomialMulGrounding

end FX1PolyAudit
