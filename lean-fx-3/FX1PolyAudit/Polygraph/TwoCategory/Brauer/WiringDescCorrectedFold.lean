import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFold — zero-axiom gate (BRAUER-MIDDLE r3, B3)

Per-declaration zero-axiom gate for R3-C: the corrected fold Prop, the whisker-free reduction over the corrected
extractor + its non-vacuity, the bounded straddle-reaches driver witness, the machine-checked terminal state, and the
honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.BrauerExt5CorrectedFoldReaches
#assert_no_axioms FX1Poly.Polygraph.brauerWords_equalMatching_conv_ofCorrectedFold
#assert_no_axioms FX1Poly.Polygraph.brauerWords_equalMatching_conv_ofCorrectedFold_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.correctedFold_straddle_reaches
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_correctedFoldTerminalState
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedFoldReduction
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedFoldDischarged

end FX1PolyAudit
