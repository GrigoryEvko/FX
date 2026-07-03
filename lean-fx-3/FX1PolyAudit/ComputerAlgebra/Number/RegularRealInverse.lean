import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealInverse

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealInverse — zero-axiom
    gate (NUM-R-5c/5d)

Per-declaration zero-axiom gate for the ℚ reciprocal kit and the real
inverse: the two margin-refutation lemmas, the sign-free scaled
reciprocal-difference bound, its two-sided `IsWithinBound` packaging,
the predecessor-shaped square with its sampling-depth lemma, and
`inverseReal` itself.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.noMarginAboveZeroNumerator
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.noMarginAboveNegativeNumerator
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.invExactSubLessEqualScaledOfMargins
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.invExactRespectsIsWithinBound
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.squaredSuccessorPredecessor
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.halfMarginLeBoundScaledIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseSamplingIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseReal

end FX1PolyAudit
