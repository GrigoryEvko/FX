import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyStraightenBandCollapse

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyStraightenBandCollapse — zero-axiom gate
(FC-3 r7)

Per-declaration zero-axiom gate for the STRAIGHTEN band-collapse engine: the whiskered-triangle firing point, the
iterated shared-leg gen-legs and legs, the whisker-vcomp distribution, and the cast-free general frame collapse.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringSnakeDoubleWhiskerCollapses
#assert_no_axioms FX1Poly.Polygraph.stringSnakeCupGenLeg
#assert_no_axioms FX1Poly.Polygraph.stringSnakeCapGenLeg
#assert_no_axioms FX1Poly.Polygraph.stringSharedLegCupLeg
#assert_no_axioms FX1Poly.Polygraph.stringSharedLegCapLeg
#assert_no_axioms FX1Poly.Polygraph.stringWhiskeredSnakeDistributesToLegs
#assert_no_axioms FX1Poly.Polygraph.stringGeneralContextFrameLegsCollapse
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringSnakeWhiskeredTriangleEngine

end FX1PolyAudit
