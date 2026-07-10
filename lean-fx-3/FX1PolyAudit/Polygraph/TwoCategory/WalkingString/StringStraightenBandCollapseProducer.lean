import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringStraightenBandCollapseProducer

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringStraightenBandCollapseProducer — zero-axiom gate
(FC-3 r7, B2 stage 1)

Per-declaration zero-axiom gate for the STRAIGHTEN band-collapse producer's leg-factorization extraction, the
merged `atomFrame` frames, and the cup half of the cast bridge.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringSharedLegLegShape
#assert_no_axioms FX1Poly.Polygraph.stringMergedCupFrame
#assert_no_axioms FX1Poly.Polygraph.stringMergedCapFrame
#assert_no_axioms FX1Poly.Polygraph.stringMergedCupFrame_convFull_cupLeg
#assert_no_axioms FX1Poly.Polygraph.stringMergedCapAlign
#assert_no_axioms FX1Poly.Polygraph.stringMergedCapEndpoint
#assert_no_axioms FX1Poly.Polygraph.stringMergedCapFrame_convFull_castCapLeg
#assert_no_axioms FX1Poly.Polygraph.stringMergedFramesAlign
#assert_no_axioms FX1Poly.Polygraph.stringMergedFramesEndpoint
#assert_no_axioms FX1Poly.Polygraph.stringMergedSharedLegFramesCollapse
#assert_no_axioms FX1Poly.Polygraph.stringZigZagBandCollapseLeft
#assert_no_axioms FX1Poly.Polygraph.stringStraightenCellDescentStep_left
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringSharedLegLegShape
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringZigZagBandCollapseLeft

end FX1PolyAudit
