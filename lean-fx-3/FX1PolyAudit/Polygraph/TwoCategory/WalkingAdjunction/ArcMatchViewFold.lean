import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcMatchViewFold — zero-axiom gate

Per-declaration zero-axiom gate for the diagram = matching bridge: the connectivity-view simulation composes,
the arc invariants supply the matching conditions package, the per-step event-node peel lifts to
`matchingSameComponent` under the tight post-step boundary-node bound, one atom bridges via the peel composed
with the shipped matching dispatch, the fold threads it end-to-end, and the seed assembles
`(arcStructureOfSpineList bc l).diagram = matchingOfSpineList bc l`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingConnectivityViewSim_trans
#assert_no_axioms FX1Poly.Polygraph.matchingSwapStateConditions_arcToWire
#assert_no_axioms FX1Poly.Polygraph.arcMatchViewSim_stepCupPeel
#assert_no_axioms FX1Poly.Polygraph.arcMatchViewSim_stepCapPeel
#assert_no_axioms FX1Poly.Polygraph.arcMatchViewSim_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcMatchConnectivityViewSim_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.arcDiagram_eq_matching

end FX1PolyAudit
