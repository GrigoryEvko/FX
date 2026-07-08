import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleToBack

/-! # FX1PolyAudit/…/ArcCupBubbleToBack — zero-axiom gate

Per-declaration zero-axiom gate for the peel-last BACK carrier (the cup-branch dual of `ArcBubbleToFront`): the
`BubblesToBack` witness, its `AtomicTraceEquiv` realization, its boundary-chain preservation, and the block-level
/ prefix-lifted images.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `ofReduceBool`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_of_bubblesToBack
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_of_bubblesToBack
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_of_bubblesToBack
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_of_bubblesToBack_withPrefix
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupBubbleToBack

end FX1PolyAudit
