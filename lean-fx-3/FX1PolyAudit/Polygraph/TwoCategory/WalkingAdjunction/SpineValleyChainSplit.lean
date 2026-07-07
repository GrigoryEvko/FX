import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyChainSplit

/-! # FX1PolyAudit/…/SpineValleyChainSplit — zero-axiom gate

Per-declaration zero-axiom gate for the Piece I realization brick: the split-a-realized-chain-at-an-arbitrary-
append `chainAppendSplit` and its readback consequence `chainToCell_splitReadback` must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.chainAppendSplit
#assert_no_axioms FX1Poly.Polygraph.chainToCell_splitReadback
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasRealizedChainAppendSplit

end FX1PolyAudit
