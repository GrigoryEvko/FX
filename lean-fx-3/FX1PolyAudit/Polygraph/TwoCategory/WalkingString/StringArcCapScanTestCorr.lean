import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapScanTestCorr

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapScanTestCorr — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — floor)

Per-declaration zero-axiom gate for the per-candidate scan-test correspondence ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_componentCorr
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_scanTestCorr
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapScanTestCorr

end FX1PolyAudit
