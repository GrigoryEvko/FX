import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealOrder

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealOrder — zero-axiom gate
    (NUM-R-4a)

Per-declaration zero-axiom gate for the ℝ positivity core: the ℚ-side
shunting and shared-addend order cancellation, the reciprocal quadruple
split, the `Type`-valued positivity witness, the quantitative tail lemma,
and the setoid transport of positivity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.natSelfLeDoubleSelfSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsAddOfSubLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsAddRightCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.reciprocalQuadrupleSplitDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RealPositivityWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.RealPositivityWitness.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.tailStaysAboveHalfMargin
#assert_no_axioms FX1Poly.ComputerAlgebra.realPositivityWitnessCongr

end FX1PolyAudit
