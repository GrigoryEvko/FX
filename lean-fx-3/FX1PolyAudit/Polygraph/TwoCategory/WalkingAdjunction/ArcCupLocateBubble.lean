import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLocateBubble

/-! # FX1PolyAudit/…/ArcCupLocateBubble — zero-axiom gate

Per-declaration zero-axiom gate for the window-free cup locate-and-bubble: a positive cup total on
a boundary-chained spine splits at a cup that bubbles to the front (dom-arity preserved), chaining
the shipped existence half with the shipped bubble producer.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupLocateAndBubble_ofCupCountPos
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupLocateBubble

end FX1PolyAudit
