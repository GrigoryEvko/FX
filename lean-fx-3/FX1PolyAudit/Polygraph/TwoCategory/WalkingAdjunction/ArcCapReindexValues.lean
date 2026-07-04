import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapReindexValues

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapReindexValues — zero-axiom gate

Per-declaration zero-axiom gate for the cap-head reindexing's value zones (peel campaign H,
seed rung, cap links-leg atoms, part 1): the below-window identity read, the past-window
up-by-two read, and the two component-avoidance atoms (left wire and event node).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadReindex_belowWindow
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadReindex_pastWindow
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadReindex_missesLeftWire
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadReindex_missesEventNode

end FX1PolyAudit
