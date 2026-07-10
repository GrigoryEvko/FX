import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringRightStraightenProducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringRightStraightenProducer — zero-axiom gate (FC-3 r8, B2)

Per-declaration zero-axiom gate for the RIGHT-handed STRAIGHTEN producer: the RIGHT reconnect, the RIGHT engine
legs / merged frames / cast bridge, the RIGHT merged collapse, the RIGHT band collapse (with its concrete probe),
and the unconditional RIGHT producer.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringSharedLegForcesSameColourRight
#assert_no_axioms FX1Poly.Polygraph.stringCupCapDeletionReconnectsRight
#assert_no_axioms FX1Poly.Polygraph.stringSnakeCupGenLegRight
#assert_no_axioms FX1Poly.Polygraph.stringSnakeCapGenLegRight
#assert_no_axioms FX1Poly.Polygraph.stringSharedLegCupLegRight
#assert_no_axioms FX1Poly.Polygraph.stringSharedLegCapLegRight
#assert_no_axioms FX1Poly.Polygraph.stringWhiskeredSnakeDistributesToLegsRight
#assert_no_axioms FX1Poly.Polygraph.stringGeneralContextFrameLegsCollapseRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedCupFrameRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedCapFrameRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedCapFrame_convFull_capLegRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedCupAlignRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedCupEndpointRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedCupFrame_convFull_castCupLegRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedFramesAlignRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedFramesEndpointRight
#assert_no_axioms FX1Poly.Polygraph.stringMergedSharedLegFramesCollapseRight
#assert_no_axioms FX1Poly.Polygraph.stringRightSnakeCollapseProbe
#assert_no_axioms FX1Poly.Polygraph.stringZigZagBandCollapseRight
#assert_no_axioms FX1Poly.Polygraph.stringStraightenCellDescentStep_ofCollapseRight
#assert_no_axioms FX1Poly.Polygraph.stringStraightenCellDescentStep_right
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringRightStraightenProducer

end FX1PolyAudit
