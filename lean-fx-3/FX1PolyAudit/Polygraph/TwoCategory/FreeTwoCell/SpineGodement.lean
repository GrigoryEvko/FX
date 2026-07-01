import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellSpineGodement — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the Godement spine step + trace equivalence + soundness of the trace
invariant: the interchange redex/reduct spine computations, the `prependSpineDiff` congruence, the full-step
trace transport, and the headline soundness `TwoCellConv ⟹ trace-equivalent spines`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.interchangeRedexSpineDiff
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.interchangeReductSpineDiff
#assert_no_axioms FX1Poly.Tier0.SpineTraceEquiv.prependSpineDiff
#assert_no_axioms FX1Poly.Tier0.TwoCellStep.spineTraceEquivDiff
#assert_no_axioms FX1Poly.Tier0.TwoCellConv.spineTraceEquiv
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSpineTraceReconstruction

end FX1PolyAudit
