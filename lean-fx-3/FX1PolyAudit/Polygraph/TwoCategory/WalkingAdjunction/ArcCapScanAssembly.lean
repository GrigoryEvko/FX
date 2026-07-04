import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapScanAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapScanAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the assembled cap-head partner-scan correspondence
(peel campaign H, rung E-3, part 4): the zone-dispatched shifted boundary read and the full
scan assembly (interleave, failing window pair dropped, shift image recognized, pointwise
map congruence).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_boundaryRead_shifted
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_partnerScanCorr

end FX1PolyAudit
