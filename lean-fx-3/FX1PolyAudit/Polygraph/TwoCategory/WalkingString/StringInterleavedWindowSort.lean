import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringInterleavedWindowSort

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringInterleavedWindowSort — zero-axiom gate (FC-3 r2, B1)

Per-declaration zero-axiom gate for the pure-block sort's transposition atom at the walking adjoint triple: the
generic adjacent-swap lift into `SpineTraceEquiv`, the three colour-pattern non-vacuity witnesses (two-colour,
gap-0 same-colour, pinned mixed cup·cap), and the two honesty markers.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringSpineAtomSwap_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringTwoColourInterleavedWindow_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringSameColourAdjacentWindow_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringPinnedMixedWindow_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxString_hasInterleavedWindowTransposition
#assert_no_axioms FX1Poly.Polygraph.fxString_hasInterleavedWindowSortAssembly

end FX1PolyAudit
