import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainSwapLeft

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWordChainSwapLeft — zero-axiom gate
(FC-3 r16, B3 word-chain substrate W4)

Per-declaration zero-axiom gate for the LEFT swap's boundary-WORD-chain preservation
(`spineBoundaryWordChained_swappedPairLeft`) and the marker.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_swappedPairLeft
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWordChainSwapLeft

end FX1PolyAudit
