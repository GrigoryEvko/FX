import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckSpineSwapConnected

/-! # FX1PolyAudit/…/ArcStuckSpineSwapConnected — zero-axiom gate

Per-declaration zero-axiom gate for the STUCK-residual swap-connectivity verdict: the two DISTINCT arc-equal
four-atom STUCK spines (`doubleSnakeOnLeft.spine`, `nestedSnakeOnLeft.spine`) ARE `SpineTraceEquiv`, decided by
exhaustive BFS saturation of the five-element swap ~-class.  Every declaration must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.nestedSnake_spine_mem_doubleSnakeSwapClass
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_doubleSnake_nestedSnake
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcStuckSpineSwapConnected

end FX1PolyAudit
