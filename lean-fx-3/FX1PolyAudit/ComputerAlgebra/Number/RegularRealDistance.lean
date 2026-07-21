import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealDistance

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealDistance — zero-axiom gate

Per-declaration zero-axiom gate for the real-level distance substrate:
the pointwise within-bound predicate, its symmetry, the two setoid
bridges (setoid-equal reals meet every nonnegative bound; the
zero-bound instance is the setoid), and the real-level slack closure.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.IsWithinRealBound
#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundOfDenotesSameReal
#assert_no_axioms FX1Poly.ComputerAlgebra.denotesSameRealOfIsWithinRealBoundZero
#assert_no_axioms FX1Poly.ComputerAlgebra.isWithinRealBoundOfForallSlack

end FX1PolyAudit
