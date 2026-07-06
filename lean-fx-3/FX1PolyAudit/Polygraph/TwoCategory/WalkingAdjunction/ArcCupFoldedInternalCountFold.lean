import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedInternalCountFold

/-! # FX1PolyAudit/…/ArcCupFoldedInternalCountFold — zero-axiom gate

Per-declaration zero-axiom gate for the internal-count folds: from the per-index fresh internal cup/cap
count agreement over the whole composite range, the two folded count lists coincide (a direct
`natRangeMapCongr` instance), completing the cup-head `tailsCancel` fold trio.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedInternalCupCountList_agrees
#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedInternalCapCountList_agrees
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupFoldedInternalCountFold

end FX1PolyAudit
