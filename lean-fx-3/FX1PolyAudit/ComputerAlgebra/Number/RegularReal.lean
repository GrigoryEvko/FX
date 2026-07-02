import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularReal

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularReal — zero-axiom gate
    (NUM-R-1)

Per-declaration zero-axiom gate for the ℝ carrier: the ε/3 shims on ℚ, the
Bishop regular-real structure, the pointwise setoid with its refl/symm/trans
(the ε/3 argument through slack closure), and the faithful ℚ ↪ ℝ constant
embedding (respects + reflects).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactIsNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactCrossPairsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsOfSubNonPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.regularityChainBoundCollapses
#assert_no_axioms FX1Poly.ComputerAlgebra.RegularReal
#assert_no_axioms FX1Poly.ComputerAlgebra.RegularReal.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.DenotesSameReal
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.constantReal
#assert_no_axioms FX1Poly.ComputerAlgebra.constantRealRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameAsOfConstantRealDenotesSame

end FX1PolyAudit
