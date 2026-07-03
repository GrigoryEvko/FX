import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewStability

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingViewStability — zero-axiom gate

Per-declaration zero-axiom gate for the connectivity view's cap stability: the view-agreement
transport, the loop and length transports, the fresh-separation kit, the cup zone classifier,
and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingViewAgrees_stepCap
#assert_no_axioms FX1Poly.Polygraph.matchingViewLoops_stepCap
#assert_no_axioms FX1Poly.Polygraph.matchingViewLength_stepCap
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNode_lt_nextFresh
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_boundaryRead_fresh_eq_false
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_fresh_boundaryRead_eq_false
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_cupLegs_eq_false
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_cupLegs_flipped_eq_false
#assert_no_axioms FX1Poly.Polygraph.stepCup_boundaryRead_zones
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingViewCapStability

end FX1PolyAudit
