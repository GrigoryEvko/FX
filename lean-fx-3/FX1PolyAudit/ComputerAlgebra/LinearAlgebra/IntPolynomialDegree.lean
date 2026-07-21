import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegree

/-! # FX1PolyAudit/.../IntPolynomialDegree — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] degree/normal-form layer: the trailing-zero trim, degree,
leading coefficient, and the theorem that trimming preserves evaluation.  `polyTrim`'s only non-list case
analysis is `Int.decEq coeff 0` on its full `isTrue`/`isFalse` enumeration; `polyTrimPreservesEval`'s `rw`s
are over data equalities.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrim
#assert_no_axioms FX1Poly.ComputerAlgebra.lastOrZero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeff
#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimPreservesEval
#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimDropsTrailingZeros
#assert_no_axioms FX1Poly.ComputerAlgebra.polyTrimKeepsInteriorZeros
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeZeroPolynomial
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffZeroPolynomial
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeLinearFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffLinearFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasDegreeAndLeadingCoefficient

end FX1PolyAudit
