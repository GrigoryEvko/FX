import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPrefixBubbleDescent

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPrefixBubbleDescent — zero-axiom gate

Per-declaration zero-axiom gate for the prefix bubble descent: the seated cap target bubbles
to the front of a boundary-chained prefix, the witness constructed by front-first recursion
with the seat descending through each arc step.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcPairSeated_bubblesThroughPrefix
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPrefixBubbleDescent

end FX1PolyAudit
