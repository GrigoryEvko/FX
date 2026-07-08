import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvFullTraceRoute

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellConvFullTraceRoute — zero-axiom gate

Per-declaration zero-axiom gate for the seed's FAITHFUL 2-cell decision, now UNCONDITIONAL: the discharged
faithful reconstruction (`adjunctionSpineTraceReconstructionFull`), the faithful trace-route decision modulo
`traceDecision` alone (`adjunctionDecideTwoCellConvFullViaTrace` / `adjunctionTwoCellConvFullDecisionModuloTrace`),
the Eckmann–Hilton smoke (`adjunctionParallelUnits_convFull`), the DISCHARGED ungated trace decision
(`adjunctionSpineTraceDecision`), the resulting unconditional faithful decision
(`adjunctionDecideTwoCellConvFull`), its accept/reject separation smokes, and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineTraceReconstructionFull
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideTwoCellConvFullViaTrace
#assert_no_axioms FX1Poly.Polygraph.adjunctionTwoCellConvFullDecisionModuloTrace
#assert_no_axioms FX1Poly.Polygraph.adjunctionParallelUnits_convFull
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineTraceDecision
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideTwoCellConvFull
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideTwoCellConvFull_accepts_parallelUnits
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideTwoCellConvFull_rejects_snake
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasFaithfulTwoCellDecisionModuloTrace

end FX1PolyAudit
