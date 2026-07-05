import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedFallback

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFusedFallback — zero-axiom gate

Per-declaration zero-axiom gate for the orphaned-leg fused fallback (peel campaign H, cup
rung 4): a fused entry whose opposite cup leg is orphaned falls back to its own index, at
both leg orientations.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFusedEntry_partnerFallback_leftLeg
#assert_no_axioms FX1Poly.Polygraph.arcCupFusedEntry_partnerFallback_rightLeg

end FX1PolyAudit
