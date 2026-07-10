import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteLift

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringValleyCommuteLift — zero-axiom gate (FC-3 r6, B2)

Per-declaration zero-axiom gate for the string COMMUTE lift: the flat-swap cell conversion and the two
disorder-drop `StringCellDescentResult` builders (both window directions), plus the honesty marker.  Must be free
of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCommutePrefixSwapCellLift
#assert_no_axioms FX1Poly.Polygraph.stringCellDescentResult_ofCommuteStep
#assert_no_axioms FX1Poly.Polygraph.stringCellDescentResult_ofCommutePrefixSwap
#assert_no_axioms FX1Poly.Polygraph.stringCellDescentResult_ofCommutePrefixSwapLeft
#assert_no_axioms FX1Poly.Polygraph.fxString_hasStringValleyCommuteLift

end FX1PolyAudit
