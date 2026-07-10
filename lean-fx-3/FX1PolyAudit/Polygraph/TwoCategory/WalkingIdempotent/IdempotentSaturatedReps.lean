import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedReps

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedReps — zero-axiom gate (conv-free skeleton)

Per-declaration zero-axiom gate for the relocated conv-FREE boundary-normalizer skeleton the native r4 idempotent
lane consumes: cell-level rigidity, the mu-iso composites, the grow tower + through-`t` canonical cell, the `t`-power
ordinal-sum lemmas, and the boundary representative `repNF` / `repFull`.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.rawCell_targetLenZero_impliesSourceLenZero
#assert_no_axioms FX1Poly.Polygraph.mulThenUnitRightWhisker
#assert_no_axioms FX1Poly.Polygraph.godementUnitMul
#assert_no_axioms FX1Poly.Polygraph.growTower
#assert_no_axioms FX1Poly.Polygraph.canonThroughT
#assert_no_axioms FX1Poly.Polygraph.growTower_zero
#assert_no_axioms FX1Poly.Polygraph.growTower_one_unfold
#assert_no_axioms FX1Poly.Polygraph.monadTPower_add_left
#assert_no_axioms FX1Poly.Polygraph.monadTPower_succ_add_left
#assert_no_axioms FX1Poly.Polygraph.composePath_monadTPower_monadT
#assert_no_axioms FX1Poly.Polygraph.whiskerRight_whiskerEq
#assert_no_axioms FX1Poly.Polygraph.monadTPower_succ_add_right
#assert_no_axioms FX1Poly.Polygraph.repNF
#assert_no_axioms FX1Poly.Polygraph.repNF_cellIndependent
#assert_no_axioms FX1Poly.Polygraph.repFull
#assert_no_axioms FX1Poly.Polygraph.repFull_boundary
#assert_no_axioms FX1Poly.Polygraph.castBoundary_id
#assert_no_axioms FX1Poly.Polygraph.repNF_of_targetLen
#assert_no_axioms FX1Poly.Polygraph.repFull_def
#assert_no_axioms FX1Poly.Polygraph.repNF_lengthCast

end FX1PolyAudit
