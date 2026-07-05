import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadCancellation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapHeadCancellation — zero-axiom gate

Per-declaration zero-axiom gate for the cap-head transport cancellation (peel campaign H,
rung E-4): two chained tails with the same composite extract over the same peeled cap
have the same fresh extract at the tail boundary — the assembled transport is injective.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_extractArc_cancel

end FX1PolyAudit
