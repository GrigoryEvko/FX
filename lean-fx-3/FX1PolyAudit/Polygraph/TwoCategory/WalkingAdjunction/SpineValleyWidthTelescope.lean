import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyWidthTelescope

/-! # FX1PolyAudit/…/SpineValleyWidthTelescope — zero-axiom gate

Per-declaration zero-axiom gate for the Piece-I length-determinacy core: the two width telescopes
(cap block drops the open-wire count by `2` per cap, cup block raises it) and the two length-determinacy
corollaries (`capLengthEq` / `cupLengthEq` from equal mid-widths).  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.pureCapBlock_widthTelescope
#assert_no_axioms FX1Poly.Polygraph.pureCupBlock_widthTelescope
#assert_no_axioms FX1Poly.Polygraph.capLength_eq_of_midWidth_eq
#assert_no_axioms FX1Poly.Polygraph.cupLength_eq_of_midWidth_eq_of_finalWidth_eq
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineValleyWidthTelescope

end FX1PolyAudit
