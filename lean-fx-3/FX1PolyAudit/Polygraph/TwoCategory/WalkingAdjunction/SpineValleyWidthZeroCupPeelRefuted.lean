import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthZeroCupPeelRefuted

/-! # FX1PolyAudit/…/SpineValleyWidthZeroCupPeelRefuted — zero-axiom gate

Per-declaration zero-axiom gate for the machine-checked refutation of the width-0 head-cup diagram peel
(Track B floor): the shared head cup, the two interchange-reordered pure-cup tails, the collapse/separate
witness facts, and the refutation `¬ WidthZeroCupHeadDiagramPeel`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.widthZeroPeelHeadMatchingsCollapse
#assert_no_axioms FX1Poly.Polygraph.widthZeroPeelTailArcsSeparate
#assert_no_axioms FX1Poly.Polygraph.not_widthZeroCupHeadDiagramPeel
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyWidthZeroCupPeelRefuted

end FX1PolyAudit
