import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.SpineGodement — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the Godement spine step + trace equivalence + soundness of the trace
invariant: the interchange redex/reduct spine computations, the `prependSpineDiff` congruence, the full-step
trace transport, and the headline soundness `TwoCellConv ⟹ trace-equivalent spines`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.interchangeRedexSpineDiff
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.interchangeReductSpineDiff
#assert_no_axioms FX1Poly.Polygraph.SpineTraceEquiv.prependSpineDiff
#assert_no_axioms FX1Poly.Polygraph.TwoCellStep.spineTraceEquivDiff
#assert_no_axioms FX1Poly.Polygraph.TwoCellConv.spineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineTraceReconstruction

end FX1PolyAudit
