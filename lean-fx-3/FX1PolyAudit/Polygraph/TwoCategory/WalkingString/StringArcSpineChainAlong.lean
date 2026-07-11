import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcSpineChainAlong

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcSpineChainAlong — zero-axiom gate
(FC-3 r22, B2 P3)

Per-declaration zero-axiom gate for the arc-fold boundary-chain advance and its marker.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringSpineBoundaryChained_alongArcSpine
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcSpineChainAlong

end FX1PolyAudit
