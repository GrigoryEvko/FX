import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcBubbleToFront — zero-axiom gate

Per-declaration zero-axiom gate for the bubble carrier: the iterated disjoint-window
transposition witness, its trace-equivalence realization, and its chain preservation.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_of_bubblesToFront
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_of_bubblesToFront

end FX1PolyAudit
