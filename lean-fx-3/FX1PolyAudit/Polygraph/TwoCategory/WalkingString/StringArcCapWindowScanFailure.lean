import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowScanFailure

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapWindowScanFailure — zero-axiom gate
(FC-3 r20, THE CLONE CAMPAIGN — floor)

Per-declaration zero-axiom gate for the folded window-pair scan failure ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowLeftScanTestFails
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowRightScanTestFails
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_windowPairScanTestsFail
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapWindowScanFailure

end FX1PolyAudit
