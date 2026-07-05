import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleConsStep

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupBubbleConsStep — zero-axiom gate

Per-declaration zero-axiom gate for the cup bubble producer's inductive step: extend an inner
cup bubble past one boundary-chained atom, minting the inert path from the window dichotomy.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionCupBubbleConsStep
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupBubbleConsStep

end FX1PolyAudit
