import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapWindowPartners

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapWindowPartners — zero-axiom gate

Per-declaration zero-axiom gate for the consumed window pair partnering each other (peel
campaign H, rung E-3, part 5): the left window index's partner scan first-hits the right
window index and vice versa at the cap-head folded end state.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowLeftPartner
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowRightPartner

end FX1PolyAudit
