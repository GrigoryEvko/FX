import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenReadback

/-! # FX1PolyAudit/…/SpineValleyStraightenReadback — zero-axiom gate

Per-declaration zero-axiom gate for Piece I STRAIGHTEN producer (iii-b) — the readback realization `stepConv`: the
readback band `readbackBand`, the cons-readback form `framedChain_readback_consForm`, the two saturated-conv cast
helpers (`saturatedConv_of_eq` / `saturatedConv_castBoundary_congr`), the width-2 straightening
`framedPairReadbackStraightens`, the width induction `framedDeleteChainReadbackConv`, and the full `stepConv`
`straightenStepConv`.  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.readbackBand
#assert_no_axioms FX1Poly.Polygraph.framedChain_readback_consForm
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_of_eq
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_castBoundary_congr
#assert_no_axioms FX1Poly.Polygraph.framedPairReadbackStraightens
#assert_no_axioms FX1Poly.Polygraph.framedDeleteChainReadbackConv
#assert_no_axioms FX1Poly.Polygraph.straightenStepConv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyStraightenReadback

end FX1PolyAudit
