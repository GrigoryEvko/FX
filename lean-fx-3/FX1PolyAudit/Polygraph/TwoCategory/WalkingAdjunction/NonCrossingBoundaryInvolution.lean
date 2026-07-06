import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingBoundaryInvolution

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/NonCrossingBoundaryInvolution — zero-axiom gate

Per-declaration zero-axiom gate for the boundary-linearization bijection (cup rung D2-prep): the
in-range bound, the involution, surjectivity, and injectivity on `[0, total)`.  The private clean
Nat plumbing is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.boundaryPosition_lt
#assert_no_axioms FX1Poly.Polygraph.boundaryPosition_involutive
#assert_no_axioms FX1Poly.Polygraph.boundaryPosition_surjective
#assert_no_axioms FX1Poly.Polygraph.boundaryPosition_injective

end FX1PolyAudit
