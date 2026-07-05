import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegSeparation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupLegSeparation — zero-axiom gate

Per-declaration zero-axiom gate for the cup leg separation (peel campaign H, cup rung 2d-iii
prep): a fresh-pair join keeps fresh probes off old probes, and after a cup step no
fresh-allocation node shares a component with any old node, in both argument orders.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_offFreshPair
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_freshOldProbes
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_oldFreshProbes

end FX1PolyAudit
