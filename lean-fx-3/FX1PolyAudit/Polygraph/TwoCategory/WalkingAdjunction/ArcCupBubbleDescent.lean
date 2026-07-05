import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleDescent

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupBubbleDescent — zero-axiom gate

Per-declaration zero-axiom gate for the cup bubble producer's full front-first descent: a cup at
the end of a boundary-chained prefix bubbles all the way to the front, moved image still a cup.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionCup_bubblesThroughPrefix
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupBubbleDescent

end FX1PolyAudit
