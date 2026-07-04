import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedTriangleReducer

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedTriangleReducer — zero-axiom gate

Per-declaration zero-axiom gate for the triangle root recognizers: the boundary cast, the
snake path/factor literals, the four recognizers with their completion probes, the
mode-dispatching root reducer, the per-rule soundness theorems, and the kernel-computed
firing smokes.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.castCellAlongBoundary
#assert_no_axioms FX1Poly.Polygraph.leftSnakeMidPath
#assert_no_axioms FX1Poly.Polygraph.rightSnakeMidPath
#assert_no_axioms FX1Poly.Polygraph.leftSnakeUnitFactor
#assert_no_axioms FX1Poly.Polygraph.leftSnakeCounitFactor
#assert_no_axioms FX1Poly.Polygraph.rightSnakeUnitFactor
#assert_no_axioms FX1Poly.Polygraph.rightSnakeCounitFactor
#assert_no_axioms FX1Poly.Polygraph.leftBareSnakeReduce?
#assert_no_axioms FX1Poly.Polygraph.rightBareSnakeReduce?
#assert_no_axioms FX1Poly.Polygraph.leftSnakePrefixCompletion?
#assert_no_axioms FX1Poly.Polygraph.leftSnakePrefixReduce?
#assert_no_axioms FX1Poly.Polygraph.rightSnakePrefixCompletion?
#assert_no_axioms FX1Poly.Polygraph.rightSnakePrefixReduce?
#assert_no_axioms FX1Poly.Polygraph.triangleReduceRoot?
#assert_no_axioms FX1Poly.Polygraph.leftBareSnakeReduce?_sound
#assert_no_axioms FX1Poly.Polygraph.rightBareSnakeReduce?_sound
#assert_no_axioms FX1Poly.Polygraph.leftSnakePrefixCompletion?_sound
#assert_no_axioms FX1Poly.Polygraph.leftSnakePrefixReduce?_sound
#assert_no_axioms FX1Poly.Polygraph.rightSnakePrefixCompletion?_sound
#assert_no_axioms FX1Poly.Polygraph.rightSnakePrefixReduce?_sound
#assert_no_axioms FX1Poly.Polygraph.triangleReduceRoot?_sound
#assert_no_axioms FX1Poly.Polygraph.leftBareSnakeReduce?_firesOnSnake
#assert_no_axioms FX1Poly.Polygraph.rightBareSnakeReduce?_firesOnSnake
#assert_no_axioms FX1Poly.Polygraph.leftSnakePrefixReduce?_firesOnPrefixedId
#assert_no_axioms FX1Poly.Polygraph.triangleReduceRoot?_firesOnLeftSnake
#assert_no_axioms FX1Poly.Polygraph.triangleReduce?
#assert_no_axioms FX1Poly.Polygraph.triangleReduce?_sound
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_sound
#assert_no_axioms FX1Poly.Polygraph.triangleReduce?_firesUnderWhisker
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_firesOnLeftSnake
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_firesOnStructuralRedex
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_firesOnRightSnake
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_firesOnLeftSnakePrefix
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_firesOnRightSnakePrefix
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_ne_none_of_step
#assert_no_axioms FX1Poly.Polygraph.saturatedReduceOnce_isNormal_of_none

end FX1PolyAudit
