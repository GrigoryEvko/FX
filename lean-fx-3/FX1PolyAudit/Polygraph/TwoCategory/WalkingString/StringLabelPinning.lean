import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelPinning

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringLabelPinning — zero-axiom gate (the r6 label-pinning crux)

Per-declaration zero-axiom gate for the r6 label-pinning crux: the two colour-separation lemmas (`F·G ≠ H·G`,
`G·H ≠ G·F`, each `left ≠ coLeft` propagated into the two-letter boundary words via `composePath` cancellation),
the label-pinning crux itself (`stringCupCod_ne_capDom`: a string cup's cod word is never a string cap's dom word),
and the two markers (the shipped-pin marker and the still-open completeness marker).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringFG_ne_stringHG
#assert_no_axioms FX1Poly.Polygraph.stringGH_ne_stringGF
#assert_no_axioms FX1Poly.Polygraph.stringCupCod_ne_capDom
#assert_no_axioms FX1Poly.Polygraph.fxString_hasLabelPinningCrux
#assert_no_axioms FX1Poly.Polygraph.fxString_hasAdjointTripleCompletenessFromPin

end FX1PolyAudit
