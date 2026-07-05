import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedDiagramFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupFoldedDiagramFold — zero-axiom gate

Per-declaration zero-axiom gate for the diagram-field fold of the cup-head partner cancel: the reusable
range-map congruence combinator, and its concrete instantiation folding the per-index fresh-partner agreement
into the whole folded diagram partner-list equality (the diagram leg of `tailsCancel` at the folded level).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natRangeMapCongr
#assert_no_axioms FX1Poly.Polygraph.arcCupFoldedDiagramPartnerList_agrees
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasNatRangeMapCongr
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupFoldedDiagramFold

end FX1PolyAudit
