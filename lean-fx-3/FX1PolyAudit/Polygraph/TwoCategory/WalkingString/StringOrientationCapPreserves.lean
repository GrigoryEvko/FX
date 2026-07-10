import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringOrientationCapPreserves

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringOrientationCapPreserves — zero-axiom gate (STRING-JOINT r2, WALL 1)

Per-declaration zero-axiom gate for the CAP orientation-preservation heart (the merge-dual of the shipped cup): the
cap-side label de-splice read, the three NEW colour deductions (LEG-straddle / SWAP-below / SWAP-above), the full CAP
case of `preserves` (`stringOrientationDiscipline_stepCap`), and the honesty marker.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringStepCap_labelRead
#assert_no_axioms FX1Poly.Polygraph.stringCapOrient_legStraddle
#assert_no_axioms FX1Poly.Polygraph.stringCapOrient_swapBelow
#assert_no_axioms FX1Poly.Polygraph.stringCapOrient_swapAbove
#assert_no_axioms FX1Poly.Polygraph.stringOrientationDiscipline_stepCap
#assert_no_axioms FX1Poly.Polygraph.fxString_hasOrientationCapPreserves

end FX1PolyAudit
