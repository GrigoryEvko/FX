import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedTarget

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFusedTarget — zero-axiom gate

Per-declaration zero-axiom gate for the closed-form rewired partner (peel campaign H, cup
rung 4): a fused entry's composite partner equals the downshifted fresh partner of the
opposite cup leg, at both leg orientations.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFusedEntry_partnerTarget_leftLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupFusedEntry_partnerTarget_rightLeg

end FX1PolyAudit
