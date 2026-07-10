import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordBubbleArcPreservation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWordBubbleArcPreservation — zero-axiom gate
(FC-3 r5, B4)

Per-declaration zero-axiom gate for the word-bubble arc-preservation transfer and its honesty marker.  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_wordBubblesToFront
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWordBubbleArcPreservation

end FX1PolyAudit
