import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordAppend

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSpineTopWordAppend — zero-axiom gate
(FC-3 r14, B3 down-payment)

Per-declaration zero-axiom gate for the two spine top-word bookkeeping bricks the width-0 sort recursion's drop
step consumes: `spineListTopWord_append`, `spineListTopWord_prefix_eq_lastDomWord`, and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineListTopWord_append
#assert_no_axioms FX1Poly.Polygraph.spineListTopWord_prefix_eq_lastDomWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSpineTopWordAppend

end FX1PolyAudit
