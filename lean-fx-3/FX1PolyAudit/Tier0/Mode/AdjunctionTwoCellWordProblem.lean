import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.AdjunctionTwoCellWordProblem

/-! # FX1PolyAudit.Tier0.Mode.AdjunctionTwoCellWordProblem — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the seed's 2-cell word problem reduced to the trace route: the
trace-route decision (NO-direction from soundness), its packaging as `DecidableTwoCellConvFor`, the residual
realization discharging the predecessors' `residual`, the full keystone decision via the trace route, and the
Eckmann–Hilton witness smoke.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.adjunctionDecideTwoCellConvViaTrace
#assert_no_axioms FX1Poly.Tier0.adjunctionTwoCellWordProblemModuloTraceRoute
#assert_no_axioms FX1Poly.Tier0.adjunctionTwoCellConvResidualFromTraceRoute
#assert_no_axioms FX1Poly.Tier0.adjunctionDecidableTwoCellConvModuloTraceRoute
#assert_no_axioms FX1Poly.Tier0.adjunctionParallelUnits_spineTraceEquiv
#assert_no_axioms FX1Poly.Tier0.fxMode_hasAdjunctionTwoCellWordProblem

end FX1PolyAudit
