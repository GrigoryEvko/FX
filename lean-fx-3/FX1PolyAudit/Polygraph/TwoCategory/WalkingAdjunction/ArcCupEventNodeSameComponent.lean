import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupEventNodeSameComponent

/-! # FX1PolyAudit/…/ArcCupEventNodeSameComponent — zero-axiom gate

Per-declaration zero-axiom gate for the cup event node's leg connectivity: after `stepCupArc`, the
fresh event node shares a connected component with both cup legs, under the fold's maintained
acyclicity `isUnionFindForest`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupEventNode_sameComponent_leftLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupEventNode_sameComponent_rightLeg
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupEventNodeLegComponent

end FX1PolyAudit
