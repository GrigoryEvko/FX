import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyCupTopTopStepTransport

/-! # FX1PolyAudit/…/ValleyCupTopTopStepTransport — zero-axiom gate

Per-declaration zero-axiom gate for the two-floor per-step lemma of the top-top offset fold (Piece II tail): one
shared top-of-stack cup step (the `diagramPartner_stepCupArc` transport shape) preserves the two-floor top-region
offset-space agreement.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.shiftedOffsetAgrees
#assert_no_axioms FX1Poly.Polygraph.topRegionOffsetAgrees
#assert_no_axioms FX1Poly.Polygraph.topRegionOffsetAgrees_step
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCupTopTopStepTransport

end FX1PolyAudit
