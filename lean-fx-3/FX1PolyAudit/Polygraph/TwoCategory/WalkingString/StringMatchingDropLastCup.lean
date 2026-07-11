import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingDropLastCup

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingDropLastCup — zero-axiom gate
(FC-3 r16, PORT 3)

Per-declaration zero-axiom gate for the adjoint-triple-seed width-0 drop-injectivity linchpin
(`stringDropLastCup_matching_injective`) and its upward companion (`stringBackAppend_matching_congr`) and
the marker.  The private reduction `stringDropStepReduce`, the re-copied `WireState`-only congruence
`stringExtractDiagram_stepCup_congr`, and the range / list / injectivity helpers are covered transitively.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringDropLastCup_matching_injective
#assert_no_axioms FX1Poly.Polygraph.stringBackAppend_matching_congr
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMatchingDropLastCupInjective

end FX1PolyAudit
