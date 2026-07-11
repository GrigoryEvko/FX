import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadCancellation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapHeadCancellation — zero-axiom gate
(FC-3 r21, THE 110-PERCENT GRIND — the cap-head transport cancellation, pure-cap)

Per-declaration zero-axiom gate for the ported cap-head transport cancellation (the #18 CANCEL rung).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_extractArc_cancel
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapHeadCancellation

end FX1PolyAudit
