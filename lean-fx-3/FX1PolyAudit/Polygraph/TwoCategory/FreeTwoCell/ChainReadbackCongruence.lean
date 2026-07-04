import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainReadbackCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ChainReadbackCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the head-frame extractor and the spineDiff readback
congruence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.headSourceEq
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineDiff_readback_congruence
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineDiffReadbackCongruence

end FX1PolyAudit
