import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyFloorHomogeneous

/-! # FX1PolyAudit/…/ValleyFloorHomogeneous — zero-axiom gate

Per-declaration zero-axiom gate for the whole-valley floor-homogeneity invariant (no valley edge crosses
the floor) and the two whole-valley union-find root facts N1 (a below-floor node keeps its root below the
floor) and N2 (a cup leg keeps its root at or above the floor) — the union-find half of the classification.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepCup_links_freshCons
#assert_no_axioms FX1Poly.Polygraph.unionFindParent_lt_of_edgesBelowFloor
#assert_no_axioms FX1Poly.Polygraph.unionFindRoot_lt_of_edgesBelowFloor
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_lt_of_edgesBelowFloor
#assert_no_axioms FX1Poly.Polygraph.edgeFloorHomogeneous
#assert_no_axioms FX1Poly.Polygraph.stepCup_edgesFloorHomogeneous
#assert_no_axioms FX1Poly.Polygraph.processSpine_edgesFloorHomogeneous_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.valleyEdgesFloorHomogeneous
#assert_no_axioms FX1Poly.Polygraph.valleyRootBelowFloor
#assert_no_axioms FX1Poly.Polygraph.valleyCupLegRootAboveFloor
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasValleyFloorHomogeneous

end FX1PolyAudit
