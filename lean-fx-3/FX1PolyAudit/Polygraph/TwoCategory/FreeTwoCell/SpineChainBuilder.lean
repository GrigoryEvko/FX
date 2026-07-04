import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineChainBuilder

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpineChainBuilder — zero-axiom gate

Per-declaration zero-axiom gate for the chain transport, the difference-list chain builder,
and the spine-anchored chain existence (the private re-anchoring seams are covered
transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.castSource
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.castTarget
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.castSource_readback
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.castTarget_readback
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineChainDiff
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.cellChain
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineChainBuilder

end FX1PolyAudit
