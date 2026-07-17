import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialLeadingCoeff

/-! # FX1PolyAudit/.../IntPolynomialLeadingCoeff — zero-axiom gate

Per-declaration zero-axiom gate for the degree↔coefficient bridge (the sixth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): `polyLeadingCoeff p = polyCoeff p (polyDegree p)`,
via the positional-reading-equals-last-trimmed-coefficient lemma.

Structural induction on the coefficient list; the only non-list case analysis is `Int.decEq coeff 0` (full
`isTrue`/`isFalse` enumeration).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffTrimLengthEqLastOrZero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffEqCoeffDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffBridgeGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLeadingCoeffBridgeZeroGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasLeadingCoeffAtDegree

end FX1PolyAudit
