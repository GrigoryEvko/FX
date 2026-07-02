import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealArithmetic

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealArithmetic — zero-axiom
    gate (NUM-R-2)

Per-declaration zero-axiom gate for the first ℝ operations: the ℚ-side shims
(double negation, negation over addition, the medial regrouping, negation and
parallel-addition respect for the two-sided bound, the two doubled-modulus
collapse identities) and the real-level negation/addition with their setoid
congruences.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.negExactNegExactDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.negExactAddExactDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactMedialDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.subExactSwapNegDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.negExactRespectsIsWithinBound
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.subExactAddDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.addExactRespectsIsWithinBound
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.reciprocalDoubleSumDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.RationalPair.ratioTwoDoubleSumDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.negReal
#assert_no_axioms FX1Poly.ComputerAlgebra.negRealRespectsDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.addReal
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealRespectsDenotesSame

end FX1PolyAudit
