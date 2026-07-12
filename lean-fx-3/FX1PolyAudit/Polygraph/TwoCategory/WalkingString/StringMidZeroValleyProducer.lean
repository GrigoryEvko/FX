import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMidZeroValleyProducer

/-! # FX1PolyAudit/…/WalkingString/StringMidZeroValleyProducer — zero-axiom gate
(FC-3 r36, the gated mid-width-`0` whole-valley producer, gate inlined)

Per-declaration zero-axiom gate for the string mid-width-`0` whole-valley `SpineTraceEquiv` producer over the
walking ADJOINT-TRIPLE signature: the block-level headline `stringMidZeroValleysWithEqualMatching_spineTraceEquiv`
(the string clone of `midZeroValleysWithEqualMatching_spineTraceEquiv`, with the r35 mid-`0` cup reconstruction
DISCHARGED and INLINED, and the two string sorts' boundary WORDS threaded as hypotheses), the two probe boundary
words, the mixed-valley truth-probe firing the WHOLE producer end-to-end, its `decide` mid-width cross-check, and
the honesty marker.  Every declaration is public, so there are no private helpers to cover transitively.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.  The
project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the trusted
cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleysWithEqualMatching_spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyProducerProbeCapWord
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyProducerProbeMidWord
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyProducer_firesOnMixedValley
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroValleyProducer_probe_midWidthIsZero
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyProducer

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringMidZeroValleysWithEqualMatching_spineTraceEquiv
#print axioms FX1Poly.Polygraph.stringMidZeroValleyProducerProbeCapWord
#print axioms FX1Poly.Polygraph.stringMidZeroValleyProducerProbeMidWord
#print axioms FX1Poly.Polygraph.stringMidZeroValleyProducer_firesOnMixedValley
#print axioms FX1Poly.Polygraph.stringMidZeroValleyProducer_probe_midWidthIsZero
#print axioms FX1Poly.Polygraph.fxString_hasMidZeroValleyProducer

end FX1PolyAudit
