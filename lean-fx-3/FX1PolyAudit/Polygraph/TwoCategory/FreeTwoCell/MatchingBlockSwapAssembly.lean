import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBlockSwapAssembly

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingBlockSwapAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the block-swap `openMap` assembly: the two rotation/shift agreement
lemmas and the four-zone pointwise witness that the reduct core's open wires are the `blockRotate` image
of the redex core's, plus the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockRotate_eq_freshShiftAbove_ofFirstBlockRange
#assert_no_axioms FX1Poly.Polygraph.blockRotate_freshShiftAbove_eq_self_ofSecondBlockRange
#assert_no_axioms FX1Poly.Polygraph.matchingCoreSwap_openWires_blockRotate
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingBlockSwapOpenWiresWitness

end FX1PolyAudit
