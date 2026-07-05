import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedBridge

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFusedBridge — zero-axiom gate

Per-declaration zero-axiom gate for the fused-component bridge (peel campaign H, cup rung
2d-v): the generic join algebra and both leg orientations of the cup-head instance.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_bridgeLegs
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_compositeSameComponent_ofFreshLegs
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_compositeSameComponent_ofFreshLegsFlipped

end FX1PolyAudit
