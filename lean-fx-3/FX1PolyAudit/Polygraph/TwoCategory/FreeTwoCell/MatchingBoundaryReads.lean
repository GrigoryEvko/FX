import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryReads

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingBoundaryReads — zero-axiom gate

Per-declaration zero-axiom gate for the boundary-node read-through kit: the length count, the
two zone reads, the cap/cup reindexing reads, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_length
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_getAt_bottomAgrees
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_getAt_top
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_stepCap_getAt_below
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_stepCap_getAt_pastPair
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_stepCup_getAt_below
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_stepCup_getAt_leftLeg
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_stepCup_getAt_rightLeg
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_stepCup_getAt_pastBlock
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingBoundaryReadKit

end FX1PolyAudit
