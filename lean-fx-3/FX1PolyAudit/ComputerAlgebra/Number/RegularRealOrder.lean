import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealOrder

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealOrder — zero-axiom gate
    (NUM-R-4a/4b/4c)

Per-declaration zero-axiom gate for the ℝ order: the ℚ-side shunting and
shared-addend order cancellation, the reciprocal quadruple split, the
`Type`-valued positivity witness, the quantitative tail lemma, the setoid
transport of positivity, the strict order and apartness with
cotransitivity, irreflexivity, the setoid congruences, and additive
compatibility.

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
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.reciprocalHalvesDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsOfNotLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.subReal
#assert_no_axioms FX1Poly.ComputerAlgebra.LessThanReal
#assert_no_axioms FX1Poly.ComputerAlgebra.RealApartnessWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.realApartnessWitnessSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.lessThanRealCotransitive
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.subExactSharedAddendCancelDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.subRealRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.lessThanRealIrrefl
#assert_no_axioms FX1Poly.ComputerAlgebra.realApartnessWitnessIrrefl
#assert_no_axioms FX1Poly.ComputerAlgebra.lessThanRealCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.realApartnessWitnessCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.realApartnessWitnessCotransitive
#assert_no_axioms FX1Poly.ComputerAlgebra.lessThanRealAddCompat
#assert_no_axioms FX1Poly.ComputerAlgebra.realApartnessWitnessAddCompat
#assert_no_axioms FX1Poly.ComputerAlgebra.lessThanRealTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.lessThanRealAsymm

end FX1PolyAudit
