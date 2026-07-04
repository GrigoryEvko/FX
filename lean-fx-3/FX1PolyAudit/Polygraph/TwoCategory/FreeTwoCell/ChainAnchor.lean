import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainAnchor

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ChainAnchor — zero-axiom gate

Per-declaration zero-axiom gate for the generator-free collapse lemmas, the atom-list chain
transport, and the anchor dichotomy.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.boundaryEq_ofGeneratorCountZero
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineDiff_eq_ofGeneratorCountZero
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.castAtoms
#assert_no_axioms FX1Poly.Polygraph.FramedSpineChain.castAtoms_readback
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineDiffChain_anchored_or_generatorFree
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasChainAnchorDichotomy

end FX1PolyAudit
