import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadStructure

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapHeadStructure — zero-axiom gate
(FC-3 r21, THE 110-PERCENT GRIND — the cap-head `FullArcStructure` transport, pure-cap)

Per-declaration zero-axiom gate for the ported cap-head full-arc-structure transport (the #17 rung).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_extractArc
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapHeadStructure

end FX1PolyAudit
