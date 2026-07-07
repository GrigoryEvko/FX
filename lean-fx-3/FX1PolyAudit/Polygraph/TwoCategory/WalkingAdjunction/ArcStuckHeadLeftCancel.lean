import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckHeadLeftCancel

/-! # FX1PolyAudit/…/ArcStuckHeadLeftCancel — zero-axiom gate

Per-declaration zero-axiom gate for the seed-level left-cancellation FAILURE: the arc-equal,
trace-equivalent double and nested snakes share a literal `cup@0` head but leave NON-trace-equivalent
tails (BFS-decided over the exhausted three-element tail swap-class).  Every declaration must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stuckSpines_headPrefix_eq
#assert_no_axioms FX1Poly.Polygraph.doubleSnakeTail_frontierExhausts
#assert_no_axioms FX1Poly.Polygraph.nestedSnakeTail_notMem_class
#assert_no_axioms FX1Poly.Polygraph.tails_notAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_notLeftCancellable_atSeed
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSeedTraceLeftCancellationFailure

end FX1PolyAudit
