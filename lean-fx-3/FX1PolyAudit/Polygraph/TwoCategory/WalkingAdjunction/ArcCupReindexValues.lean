import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexValues

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupReindexValues — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head reindexing's value zones (peel campaign H,
seed rung, links-leg atoms, part 1): the below-width unfolding, the four zone reads, the
below-boundary value bound, and the event-node avoidance atom.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcHeadReindex_readsBelow
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_belowWindow
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_leftLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_rightLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_pastWindow
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_valueBelowBoundary
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadReindex_missesEventNode

end FX1PolyAudit
