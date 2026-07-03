import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewStability

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingViewStability — zero-axiom gate

Per-declaration zero-axiom gate for the connectivity view's step stability: the cap and cup
view-agreement transports, the loop and length transports, the fresh-separation kit, the cup
zone classifier, the per-class join evaluations, and the honesty markers.

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
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_boundaryReads
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_boundaryRead_leftLeg
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_boundaryRead_rightLeg
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_leftLeg_boundaryRead
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_rightLeg_boundaryRead
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_leftLeg_rightLeg
#assert_no_axioms FX1Poly.Polygraph.stepCup_isSameComponent_rightLeg_leftLeg
#assert_no_axioms FX1Poly.Polygraph.matchingViewAgrees_stepCup
#assert_no_axioms FX1Poly.Polygraph.matchingViewLoops_stepCup
#assert_no_axioms FX1Poly.Polygraph.matchingViewLength_stepCup
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingViewCapStability
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingViewCupStability

end FX1PolyAudit
