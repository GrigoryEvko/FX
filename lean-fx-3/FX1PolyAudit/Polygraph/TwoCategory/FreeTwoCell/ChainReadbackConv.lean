import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainReadbackConv

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ChainReadbackConv — zero-axiom gate

Per-declaration zero-axiom gate for the cast extrusion, the context-absorption pair, the
generalized readback conversion, and the chain-existence headline.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.vcomp_castBoundaryLeft
#assert_no_axioms FX1Poly.Polygraph.whiskerLeftAbsorb_convFull
#assert_no_axioms FX1Poly.Polygraph.whiskerRightAbsorb_convFull
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineChainDiff_readback_convFull
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.cellChain_readback_convFull
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasChainReadbackConv

end FX1PolyAudit
