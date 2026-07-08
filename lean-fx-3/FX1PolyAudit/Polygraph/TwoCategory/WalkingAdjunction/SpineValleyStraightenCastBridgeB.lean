import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenCastBridgeB

/-! # FX1PolyAudit/…/SpineValleyStraightenCastBridgeB — zero-axiom gate

Per-declaration zero-axiom gate for THE CAST BRIDGE (handedness B): the two merged frames (`mergedCupFrameB` /
`mergedCapFrameB`), the two alignment casts (`mergedFramesAlignB` / `mergedFramesEndpointB`), and the collapse
itself (`mergedSharedLegFramesCollapseB`).  The private cast helpers used inside the collapse are covered
transitively by the collapse's axiom check.  Every declaration must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mergedCupFrameB
#assert_no_axioms FX1Poly.Polygraph.mergedCapFrameB
#assert_no_axioms FX1Poly.Polygraph.mergedFramesAlignB
#assert_no_axioms FX1Poly.Polygraph.mergedFramesEndpointB
#assert_no_axioms FX1Poly.Polygraph.mergedSharedLegFramesCollapseB
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenCastBridgeB

end FX1PolyAudit
