import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RationalPair

/-! # FX1PolyAudit/ComputerAlgebra/Number/RationalPair — zero-axiom gate
    (NUM-Q-1)

Per-declaration zero-axiom gate for the ℚ carrier: the successor-shaped pair, the
positive denominator read-back, and the decidable cross-multiplication setoid with
its reflexivity/symmetry/transitivity laws.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mk
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denominatorInt
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denominatorIntIsPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.DenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.decideDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denotesSameAsRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denotesSameAsSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denotesSameAsTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExact
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactNumerator
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactDenominatorInt
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mulExact
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mulExactNumerator
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mulExactDenominatorInt
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.negExact
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactCongrLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactCongrRight
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactRespectsDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mulExactCongrLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mulExactCongrRight
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.mulExactRespectsDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.negExactRespectsDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.LessEqualAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.decideLessEqualAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.LessThanAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.decideLessThanAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsOfLessThan
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsTotal
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsOfDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.denotesSameAsOfLessEqualBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsCongrLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsCongrRight
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessThanAsTrichotomy

end FX1PolyAudit
