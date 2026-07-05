import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseLocate

/-! # FX1PolyAudit/…/ArcCupCaseLocate — zero-axiom gate

Per-declaration zero-axiom gate for the cup case's non-orbit inputs: from a cup-arity head, a
boundary-chained second spine, and arc-structure equality, the second spine splits at a cup that
bubbles to the front — the located split, the bubble witness, and the moved dom-arity pin.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupCase_locateAndBubble
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupCaseLocate

end FX1PolyAudit
