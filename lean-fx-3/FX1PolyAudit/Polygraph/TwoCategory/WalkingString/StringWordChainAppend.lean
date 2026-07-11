import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordChainAppend

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWordChainAppend — zero-axiom gate
(FC-3 r16, B3 word-chain substrate W1-W3)

Per-declaration zero-axiom gate for the boundary-WORD-chain append / peel / snoc substrate
(`spineBoundaryWordChained_prefix_ofAppend`, `spineBoundaryWordChained_append`,
`spineBoundaryWordChained_snoc`) and the marker.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_prefix_ofAppend
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_append
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryWordChained_snoc
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWordChainAppend

end FX1PolyAudit
