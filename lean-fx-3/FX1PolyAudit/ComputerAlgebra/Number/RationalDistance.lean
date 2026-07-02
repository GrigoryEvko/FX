import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RationalDistance

/-! # FX1PolyAudit/ComputerAlgebra/Number/RationalDistance — zero-axiom gate
    (NUM-R-0)

Per-declaration zero-axiom gate for the two-sided rational distance kit:
subtraction, the structurally-positive bound constructors, the two-sided
predicate with decidability/symmetry/monotonicity/self-distance/congruence,
the subtraction chain law, and the triangle inequality.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.subExact
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.ratioOfNatSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.reciprocalOfSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.IsWithinBound
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.decideIsWithinBound
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundOfBoundLessEqual
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundSelfOfNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.subExactRespectsDenotesSameAs
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundCongrLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundCongrRight
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundCongrBound
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.subExactChainDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundTriangle
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.ratioOfNatSuccIsNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.ratioOfNatSuccSumDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.lessEqualAsOfForallSlack
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.isWithinBoundOfForallSlack

end FX1PolyAudit
