import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealOrderTightness

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealOrderTightness — zero-axiom gate
    (NUM-R-5c)

Per-declaration zero-axiom gate for the ℝ order's tightness and setoid
congruence: negation antitone on the ℚ order, the two ε/3 and slack-tail
bound collapses, tightness (mutual `≤` gives the setoid), the setoid-
invariance of nonnegativity, and the non-strict order's setoid
congruence on both endpoints.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsNegBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.tightnessChainBoundCollapses
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactNegLeftDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.congruenceSlackTailCollapses
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.congruenceSlackTailCollapsesShaped
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealOfLessEqualBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealTight
#assert_no_axioms FX1Poly.ComputerAlgebra.realNonNegativeRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.lessEqualRealAddCompat
#assert_no_axioms FX1Poly.ComputerAlgebra.fxRegularReal_hasRealOrderTightness

end FX1PolyAudit
