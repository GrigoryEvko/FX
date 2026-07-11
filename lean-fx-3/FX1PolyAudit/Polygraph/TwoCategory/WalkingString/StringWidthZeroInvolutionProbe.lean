import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroInvolutionProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroInvolutionProbe — zero-axiom gate
(FC-3 r14, B1)

Per-declaration zero-axiom gate for the width-0 partner INVOLUTION firing at the string signature: the
string-signature specialisation of the widened involution (`stringWidthZeroPureCup_partnerInvolution`), the
concrete r13 mixed-witness matching (`stringMixedWidthZero_matchingPartner`, `_topCount`), the concrete firing
(`stringMixedWidthZero_partnerInvolution`, `_involutionAtZero`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroPureCup_partnerInvolution
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZero_matchingPartner
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZero_topCount
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZero_partnerInvolution
#assert_no_axioms FX1Poly.Polygraph.stringMixedWidthZero_involutionAtZero
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWidthZeroInvolutionProbe

end FX1PolyAudit
