import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapScanTestCorr

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapScanTestCorr — zero-axiom gate

Per-declaration zero-axiom gate for the per-candidate scan-test correspondence at the cap
head (peel campaign H, rung E-3, part 3b): the collapsed folded component correspondence
and the whole exclude-and-root test correspondence in `findPartnerScan_mapCongr`'s
pointwise shape.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_componentCorr
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_scanTestCorr

end FX1PolyAudit
