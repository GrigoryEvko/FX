import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupScanTestCorr

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupScanTestCorr — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head per-candidate scan-test correspondence
(peel campaign H, cup rung 2a): the pointwise folded component correspondence (the REAL
leg join on the fresh side) and the whole exclude-and-root test correspondence in
`findPartnerScan_mapCongr`'s pointwise shape.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_componentCorr
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_scanTestCorr

end FX1PolyAudit
