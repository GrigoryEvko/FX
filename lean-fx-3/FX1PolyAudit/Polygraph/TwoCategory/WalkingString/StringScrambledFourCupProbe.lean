import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringScrambledFourCupProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringScrambledFourCupProbe — zero-axiom gate (FC-3 r13, B2)

Per-declaration zero-axiom gate for the scrambled four-cup transposition truth-probe: the trailing-context cup
(`stringProbeRestCup`), the probe (`stringScrambledFourCup_traceEquivAndTopWord`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringProbeRestCup
#assert_no_axioms FX1Poly.Polygraph.stringScrambledFourCup_traceEquivAndTopWord
#assert_no_axioms FX1Poly.Polygraph.fxString_hasScrambledFourCupProbe

end FX1PolyAudit
