import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedFallback

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFusedFallback — zero-axiom gate

Per-declaration zero-axiom gate for the orphaned-leg fused fallback (peel campaign H, cup
rung 4): the left-leg-fused entry with an orphaned right leg falls back to its own index.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFusedEntry_partnerFallback_leftLeg

end FX1PolyAudit
