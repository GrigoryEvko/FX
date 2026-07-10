import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcMiddleLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcMiddleLedger — zero-axiom gate (BRAUER-MIDDLE r1, B2/B3/B4)

Per-declaration zero-axiom gate for the conv-to-standard-form partial fold (`standardFormWordExt_crossingOnly`,
`pureCrossingWord_convReaches_standardFormExt`, `straddleWord_convReaches_standardFormExt`), the terminal-state
decomposition (`fxBrauer_arcMiddleTerminalState`), and the two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.standardFormWordExt_crossingOnly
#assert_no_axioms FX1Poly.Polygraph.pureCrossingWord_convReaches_standardFormExt
#assert_no_axioms FX1Poly.Polygraph.straddleWord_convReaches_standardFormExt
#assert_no_axioms FX1Poly.Polygraph.pureCrossingWord_convReaches_standardFormExt_r9
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_arcMiddleTerminalState
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStandardFormConvReach
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerMiddleFullFold

end FX1PolyAudit
