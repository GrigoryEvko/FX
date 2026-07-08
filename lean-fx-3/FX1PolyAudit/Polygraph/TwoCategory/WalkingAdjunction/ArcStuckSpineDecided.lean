import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckSpineDecided

/-! # FX1PolyAudit/…/ArcStuckSpineDecided — zero-axiom gate

Per-declaration zero-axiom gate for RUNNING the two-directional decider on the STUCK residual: the gated FREE-6c
decision procedure `decideAtomicTraceEquivViaSaturation`, discharged by the computable frontier-exhaustion gate,
returns `isTrue` on the two DISTINCT arc-equal four-atom stuck spines (`doubleSnakeOnLeft.spine`,
`nestedSnakeOnLeft.spine`).  Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `ofReduceBool`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stuckSnakes_didExhaustFrontier
#assert_no_axioms FX1Poly.Polygraph.decideAtomicTraceEquivStuck
#assert_no_axioms FX1Poly.Polygraph.decideAtomicTraceEquivStuck_isAccepting
#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_doubleSnake_nestedSnake_byDecider
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcStuckSpineDecidedTrue

end FX1PolyAudit
