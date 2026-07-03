import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealInverse

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealInverse — zero-axiom
    gate (NUM-R-5c)

Per-declaration zero-axiom gate for the ℚ reciprocal kit: the two
margin-refutation lemmas, the sign-free scaled reciprocal-difference
bound, and its two-sided `IsWithinBound` packaging.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.noMarginAboveZeroNumerator
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.noMarginAboveNegativeNumerator
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.invExactSubLessEqualScaledOfMargins
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.invExactRespectsIsWithinBound

end FX1PolyAudit
