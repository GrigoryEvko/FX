import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainGodementStep

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ChainGodementStep — zero-axiom gate

Per-declaration zero-axiom gate for the Nat sum split, the hcomp-order conversion, the swap
core, and the Godement chain lift headline pair.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.sumEqZero_impliesComponentsZero
#assert_no_axioms FX1Poly.Polygraph.hcompOrder_twoCellConv
#assert_no_axioms FX1Poly.Polygraph.transposedBlocksChains_readback_convFull
#assert_no_axioms FX1Poly.Polygraph.SpineGodementStep.readback_convFull
#assert_no_axioms FX1Poly.Polygraph.SpineGodementStep.preservesChainability
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasChainGodementStep

end FX1PolyAudit
