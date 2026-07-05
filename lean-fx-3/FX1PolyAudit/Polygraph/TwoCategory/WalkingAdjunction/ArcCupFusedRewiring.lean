import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedRewiring

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFusedRewiring — zero-axiom gate

Per-declaration zero-axiom gate for the entry-level fused rewiring (peel campaign H, cup
rung 2d-v close): the zone-dispatched cup boundary read and both leg orientations of the
fused partner rewiring.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_boundaryRead_shifted
#assert_no_axioms FX1Poly.Polygraph.arcCupFusedEntry_partnerRewires_leftLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupFusedEntry_partnerRewires_rightLeg

end FX1PolyAudit
