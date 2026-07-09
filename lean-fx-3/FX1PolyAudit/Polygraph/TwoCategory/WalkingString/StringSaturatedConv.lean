import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSaturatedConv

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSaturatedConv — zero-axiom gate

Per-declaration zero-axiom gate for the SATURATED walking-adjoint-triple 2-cell convertibility: the four
generators embedded as free cells, the four identity cells, the four snakes, the saturated relation, its `ofConv`
embedding, the four triangle witnesses, the shared-`G` coherence, the whiskered smoke, and the established marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringUnitLower
#assert_no_axioms FX1Poly.Polygraph.stringCounitLower
#assert_no_axioms FX1Poly.Polygraph.stringUnitUpper
#assert_no_axioms FX1Poly.Polygraph.stringCounitUpper
#assert_no_axioms FX1Poly.Polygraph.stringIdentityF
#assert_no_axioms FX1Poly.Polygraph.stringIdentityG
#assert_no_axioms FX1Poly.Polygraph.stringIdentityH
#assert_no_axioms FX1Poly.Polygraph.stringSnakeF
#assert_no_axioms FX1Poly.Polygraph.stringSnakeGlo
#assert_no_axioms FX1Poly.Polygraph.stringSnakeGhi
#assert_no_axioms FX1Poly.Polygraph.stringSnakeH
#assert_no_axioms FX1Poly.Polygraph.StringSaturatedTwoCellConv
#assert_no_axioms FX1Poly.Polygraph.StringSaturatedTwoCellConv.ofConv
#assert_no_axioms FX1Poly.Polygraph.stringTriangleFHolds
#assert_no_axioms FX1Poly.Polygraph.stringTriangleGloHolds
#assert_no_axioms FX1Poly.Polygraph.stringTriangleGhiHolds
#assert_no_axioms FX1Poly.Polygraph.stringTriangleHHolds
#assert_no_axioms FX1Poly.Polygraph.stringSnakeGlo_conv_stringSnakeGhi
#assert_no_axioms FX1Poly.Polygraph.stringTriangleFWhiskeredHolds
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointTripleSaturatedConvRelation

end FX1PolyAudit
