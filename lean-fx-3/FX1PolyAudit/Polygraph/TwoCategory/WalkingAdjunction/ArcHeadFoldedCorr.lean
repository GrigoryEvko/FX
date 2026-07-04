import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedCorr

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcHeadFoldedCorr — zero-axiom gate

Per-declaration zero-axiom gate for the head-cancellation component correspondence at the
folded end states (peel campaign H, fold rung closed): the cup-head and cap-head seed pairs
threaded through the whole-spine component fold.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_cupHeadFolded
#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_capHeadFolded

end FX1PolyAudit
