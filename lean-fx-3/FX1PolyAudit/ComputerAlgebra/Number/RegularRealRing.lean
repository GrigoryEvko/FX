import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealRing

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealRing — zero-axiom gate
    (NUM-R-4)

Per-declaration zero-axiom gate for the `RegularReal` commutative-ring laws:
the deep-sample drift bridge, the negation-passing bricks, the additive-group
laws (comm, zero identities, right inverse, associativity), the ℚ zero-product
identities, the multiplicative identities/zero laws, commutativity, and the
compare-bound collapse feeding additive associativity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.deepSampleDriftIsWithinSetoidBound
#assert_no_axioms FX1Poly.ComputerAlgebra.negRealNegRealDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.negRealAddRealDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealComm
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mulExactZeroRightDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.mulExactZeroLeftDenotesSame
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealOneRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealOneLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealComm
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealAssocCompareBoundCollapses
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealAssoc

end FX1PolyAudit
