import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapRootAtlas

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapRootAtlas — zero-axiom gate

Per-declaration zero-axiom gate for the cap root atlas: the merged-links freshness bound, the
merged-root old-node bound, the event-node root, old-node root locality through the cap, the
parentless range above, and the old-event count collapse to the merged links.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capMerge_all_below
#assert_no_axioms FX1Poly.Polygraph.capMerge_root_below
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_root_event
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_root_old
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_root_above
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_countOldEvents_congr

end FX1PolyAudit
