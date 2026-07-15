import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExprSimplify

/-! # FX1PolyAudit.Axis.Type.Level.LevelExprSimplify01

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Level.LevelExprSimplify` (part 1 of 7).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_idempotent

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_idempotent_nonzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_left_identity

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_right_identity

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_left_identity

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_right_collapse

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_both_zero

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lsucc_lzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lvar_zero

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lmax_distinct

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_limax_non_lzero_codomain

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lzero_idempotent

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_lvar_zero_idempotent

#assert_no_axioms FX1Poly.Universe.LevelExpr.size

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_pos

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_size_le

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lvar

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lsucc

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lmax

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_limax

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_idempotent

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsPhaseANormalForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_produces_normal_form

#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_isNormalForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.lvar_isNormalForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStructurallyNormalForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_produces_isStructurallyNormalForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsStructurallyNormalForm.toFixedPoint

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_isStructurallyNormal_and_fixed

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_lmax_left

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_lmax_right

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_limax_left

#assert_no_axioms FX1Poly.Universe.LevelExpr.size_lt_limax_right

#assert_no_axioms FX1Poly.Universe.LevelExpr.lzero_size_lt_limax

#assert_no_axioms FX1Poly.Universe.LevelExpr.IsPhaseANormalForm.toStructurallyNormal

#assert_no_axioms FX1Poly.Universe.LevelExpr.isPhaseANormalForm_iff_isStructurallyNormalForm

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_self

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_zero_left

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_zero_right

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lvar

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lsucc

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_lmax

#assert_no_axioms FX1Poly.Universe.LevelExpr.denote_limax

end FX1PolyAudit
