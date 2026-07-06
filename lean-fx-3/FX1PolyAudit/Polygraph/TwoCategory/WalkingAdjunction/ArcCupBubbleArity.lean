import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleArity

/-! # FX1PolyAudit/…/ArcCupBubbleArity — zero-axiom gate

Per-declaration zero-axiom gate for the cup seat-tracking rung 0: the bubble preserves the
target's generator arities, so both cup arity pins drop out of the witness (the window pin
remains the orbit-search residual).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.bubblesToFront_movedGeneratorArities
#assert_no_axioms FX1Poly.Polygraph.bubblesToFront_movedDomArity
#assert_no_axioms FX1Poly.Polygraph.bubblesToFront_movedCodArity
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupBubbleArity

end FX1PolyAudit
