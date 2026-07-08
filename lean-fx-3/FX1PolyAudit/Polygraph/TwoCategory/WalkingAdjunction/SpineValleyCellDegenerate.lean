import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellDegenerate

/-! # FX1PolyAudit/…/SpineValleyCellDegenerate — zero-axiom gate

Per-declaration zero-axiom gate for the Tier-D degenerate dispatch + the FULL `CellValleyTraceEquiv` lift
(Track B, Brick 4 close-out): the width-0 pure-cup determinacy residual interface, the fully-proven empty-source
case (a), the mid-width-0 case (b) residual interface, and the three-way lift.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.WidthZeroPureCupDeterminacy
#assert_no_axioms FX1Poly.Polygraph.widthZeroPureCupDeterminacy_holds
#assert_no_axioms FX1Poly.Polygraph.degenerateEmptySource_of_widthZero
#assert_no_axioms FX1Poly.Polygraph.MidZeroValleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.cellValleyTraceEquiv_of_widthZero_of_midZero
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyCellDegenerate

end FX1PolyAudit
