import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineTopWordSwapInvariant

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSpineTopWordSwapInvariant — zero-axiom gate
(FC-3 r13, N2)

Per-declaration zero-axiom gate for the spine top-word transposition invariance: the single-swap invariance
(`spineListTopWord_swapInvariant`), the full atomic-closure invariance (`spineListTopWord_atomicTraceEquiv`), and the
marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineListTopWord_swapInvariant
#assert_no_axioms FX1Poly.Polygraph.spineListTopWord_atomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSpineTopWordSwapInvariant

end FX1PolyAudit
