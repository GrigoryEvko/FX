import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescExtractorFold

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescExtractorFold — zero-axiom gate (BRAUER-MIDDLE r2, B3)

Per-declaration zero-axiom gate for the fold + decision assembly: the symm/trans glue
(`brauerConvFree8_common_target` + its non-vacuity), the fold `Prop` (`BrauerExt5FoldReaches`), the conditional
completeness reduction (`brauerWords_equalMatching_conv_ofFold` + its non-vacuity), the machine-checked terminal state
(`fxBrauer_arcExtractorFoldTerminalState`), and the two honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_common_target
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree8_common_target_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.BrauerExt5FoldReaches
#assert_no_axioms FX1Poly.Polygraph.brauerWords_equalMatching_conv_ofFold
#assert_no_axioms FX1Poly.Polygraph.brauerWords_equalMatching_conv_ofFold_nonVacuity
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_arcExtractorFoldTerminalState
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5FoldReduction
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasExt5FoldDischarged

end FX1PolyAudit
