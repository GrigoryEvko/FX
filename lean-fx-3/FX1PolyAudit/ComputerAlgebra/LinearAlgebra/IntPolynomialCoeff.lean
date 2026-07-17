import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCoeff

/-! # FX1PolyAudit/.../IntPolynomialCoeff — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] positional coefficient accessor (the fifth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the accessor and the four coefficient ring
homomorphisms (scale/add/neg/sub) plus the monomial-at-its-degree fact — the leading-term-cancellation
substrate for the pseudo-division degree-decrease.

The accessor recurses structurally on the coefficient list and the position; every arithmetic step routes
through the corpus `Int` lemmas.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffScale
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffSub
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffMonomialAt
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffPastEnd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffScaleGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasCoefficientHomomorphisms

end FX1PolyAudit
