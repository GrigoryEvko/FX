import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyRedexStep

/-! # FX1PolyAudit/…/SpineValleyRedexStep — zero-axiom gate

Per-declaration zero-axiom gate for the Piece I redex-step disorder drop at arbitrary depth and the two
`CellDescentResult` builders: every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold_le_cons2
#assert_no_axioms FX1Poly.Polygraph.crossInversionCount_swap_adjacent
#assert_no_axioms FX1Poly.Polygraph.crossInversionCount_le_delete2
#assert_no_axioms FX1Poly.Polygraph.countInversions_prefixSwap_lt
#assert_no_axioms FX1Poly.Polygraph.countInversions_prefixDelete_lt
#assert_no_axioms FX1Poly.Polygraph.countBelowThreshold_cons2_slotCongr
#assert_no_axioms FX1Poly.Polygraph.crossInversionCount_cons2_slotCongr
#assert_no_axioms FX1Poly.Polygraph.countInversions_cons2_slotCongr
#assert_no_axioms FX1Poly.Polygraph.countInversions_prefixCons2_slotCongr
#assert_no_axioms FX1Poly.Polygraph.spineDisorder_swap_lt
#assert_no_axioms FX1Poly.Polygraph.spineDisorder_delete_lt
#assert_no_axioms FX1Poly.Polygraph.cellDescentResult_ofCommuteStep
#assert_no_axioms FX1Poly.Polygraph.cellDescentResult_ofStraightenStep
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyRedexStepDrop

end FX1PolyAudit
