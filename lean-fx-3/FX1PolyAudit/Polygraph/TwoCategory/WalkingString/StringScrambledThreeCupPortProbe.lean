import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringScrambledThreeCupPortProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringScrambledThreeCupPortProbe — zero-axiom gate
(FC-3 r16, B1/B3 anti-vacuity)

Per-declaration zero-axiom gate for the concrete three-cup width-0 port truth-probe
(`stringScrambledThreeCup_lastCupShortChord`, `stringScrambledThreeCup_wordChainThreads`) plus the
chain / pure-cup witnesses and the marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringProbeThreeCup_chained
#assert_no_axioms FX1Poly.Polygraph.stringProbeThreeCup_pureCup
#assert_no_axioms FX1Poly.Polygraph.stringScrambledThreeCup_lastCupShortChord
#assert_no_axioms FX1Poly.Polygraph.stringScrambledThreeCup_wordChainThreads
#assert_no_axioms FX1Poly.Polygraph.fxString_hasScrambledThreeCupPortProbe

end FX1PolyAudit
