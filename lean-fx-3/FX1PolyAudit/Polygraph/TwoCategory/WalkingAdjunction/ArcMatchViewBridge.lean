import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewBridge

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcMatchViewBridge — zero-axiom gate

Per-declaration zero-axiom gate for the arc/matching per-step event-node peel: a cup/cap arc step's
boundary same-component view (projected via `arcToWire`) equals the corresponding matching step's, because
the fresh event node is component-invisible.  The crux ingredient of the diagram = matching bridge.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcToWire
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCupArc_eq_stepCup
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCap_eq_wireJoin
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_eq_stepCap

end FX1PolyAudit
