import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroPureCupSort

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroPureCupSort — zero-axiom gate
(FC-3 r17, THE NOVEL ASSEMBLY)

Per-declaration zero-axiom gate for the width-0 pure-cup determinacy inhabitation: the fueled partner-locate
wrapper (`stringMatchingLocateAux`), the inhabited determinacy (`stringWidthZeroPureCupDeterminacyShared_proof`),
the now-unconditional case-(a) consumer (`stringDegenerateEmptySource_of_widthZero_proved`), the back-append
congruence (`stringSpineTraceEquiv_backAppendCongr`), the two concrete truth-probes, and the marker.  Each must
be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` (asserting a public decl also
gates its private fueled helpers `stringMatchingLocateAuxFueled` / `stringMatchingPureCupSpineSortFueled`
transitively). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMatchingLocateAux
#assert_no_axioms FX1Poly.Polygraph.stringSpineTraceEquiv_backAppendCongr
#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroPureCupDeterminacyShared_proof
#assert_no_axioms FX1Poly.Polygraph.stringDegenerateEmptySource_of_widthZero_proved
#assert_no_axioms FX1Poly.Polygraph.stringLocateThreeCupProbe_partnerWindowZero
#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroPureCupSort_firesOnThreeCupRainbow
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWidthZeroPureCupSort

end FX1PolyAudit
