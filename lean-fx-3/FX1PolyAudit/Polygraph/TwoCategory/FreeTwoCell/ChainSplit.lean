import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainSplit

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ChainSplit — zero-axiom gate

Per-declaration zero-axiom gate for the tail extractor, chain uniqueness, the split inverse to
the chain builder, and the split readback conversion.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.tailChain
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.subsingletonEq
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineChainSplit
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.split_readback_convFull
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineChainSplit

end FX1PolyAudit
