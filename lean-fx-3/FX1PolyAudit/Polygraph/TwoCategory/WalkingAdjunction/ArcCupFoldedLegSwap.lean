import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedLegSwap

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFoldedLegSwap — zero-axiom gate

Per-declaration zero-axiom gate for the leg-swap kill at the two folded cup runs: the
instantiated cross-run refutation and the fused-attachment agreement corollary.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedLegSwap_impossible
#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedLegAttachment_agrees
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupFoldedLegSwap

end FX1PolyAudit
