import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroSnakeProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroSnakeProbe — zero-axiom gate
(FC-3 r14, B2 down-payment)

Per-declaration zero-axiom gate for the width-0 snake exclusion firing at the string signature: the
string-signature specialisation of the widened `matchingForwardChordsNotAdjacent`
(`stringWidthZeroPureCup_forwardChordsNotAdjacent`) and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroPureCup_forwardChordsNotAdjacent
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWidthZeroSnakeProbe

end FX1PolyAudit
