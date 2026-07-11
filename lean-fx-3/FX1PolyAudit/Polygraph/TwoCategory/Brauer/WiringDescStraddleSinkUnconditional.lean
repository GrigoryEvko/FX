import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraddleSinkUnconditional

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescStraddleSinkUnconditional — zero-axiom gate (BRAUER r33)

Per-declaration zero-axiom gate for the unconditional straddle sink rung: the two straddle-count head reductions, the
cup-headed boundary vanishing, the discharged r32 `primDrop` residual, the hypothesis-free straddle rung and its clean
instance, the two-cell reduction through the straddle, the honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.straddleCount_crossingHead
#assert_no_axioms FX1Poly.Polygraph.straddleCount_cupCrossingCons
#assert_no_axioms FX1Poly.Polygraph.straddleWindowBit_cupSecond_eq_zero
#assert_no_axioms FX1Poly.Polygraph.straddleBoundaryCount_cupHead
#assert_no_axioms FX1Poly.Polygraph.straddleCount_straddleSlide_drop
#assert_no_axioms FX1Poly.Polygraph.arcSink_straddle_unconditional
#assert_no_axioms FX1Poly.Polygraph.arcSink_straddle_unconditional_clean
#assert_no_axioms FX1Poly.Polygraph.arcSinkFold_throughStraddle_demo
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddlePrimDropDischarged
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleSinkUnconditional
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasArcSinkThroughStraddle
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasStraddleGlobalFuelBounded
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_straddleSinkUnconditionalTerminalState

end FX1PolyAudit
