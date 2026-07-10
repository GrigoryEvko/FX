import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyStraightenReadback

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyStraightenReadback — zero-axiom gate (FC-3 r6, B1)

Per-declaration zero-axiom gate for the string STRAIGHTEN scaffolding: the readback band, the two cast helpers, the
snake-prefix straightening, the RV middle-four step and width induction on the readback, the `stepConv`, the
STRAIGHTEN `StringCellDescentResult` builder, the collapse-gated producer, and the two markers (the scaffolding
marker and the band-collapse wall record).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringReadbackBand
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_of_eq
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedConv_castBoundary_congr
#assert_no_axioms FX1Poly.Polygraph.stringSnakePrefixStraightens
#assert_no_axioms FX1Poly.Polygraph.stringFramedPairReadbackStraightens
#assert_no_axioms FX1Poly.Polygraph.stringFramedDeleteChainReadbackConv
#assert_no_axioms FX1Poly.Polygraph.stringStraightenStepConv
#assert_no_axioms FX1Poly.Polygraph.stringCellDescentResult_ofStraightenStep
#assert_no_axioms FX1Poly.Polygraph.stringStraightenCellDescentStep_ofCollapse
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringValleyStraightenReadback
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringValleyStraightenBandCollapse

end FX1PolyAudit
