import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthZeroCupPeel

/-! # FX1PolyAudit/…/SpineValleyWidthZeroCupPeel — zero-axiom gate

Per-declaration zero-axiom gate for the width-0 pure-cup determinacy reduction to a positivity-FREE head-cup
diagram peel (Track B): the head-cup rigidity, the isolated positivity-free residual interface, and the
first-cup-peel reduction of `WidthZeroPureCupDeterminacy`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.cupHeadChainedZero_eq
#assert_no_axioms FX1Poly.Polygraph.WidthZeroCupHeadDiagramPeel
#assert_no_axioms FX1Poly.Polygraph.widthZeroPureCupDeterminacy_of_headDiagramPeel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyWidthZeroCupPeel

end FX1PolyAudit
