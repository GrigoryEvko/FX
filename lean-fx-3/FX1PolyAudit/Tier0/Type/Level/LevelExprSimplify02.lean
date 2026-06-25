import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Type.Level.LevelExprSimplify

/-! # FX1PolyAudit.Tier0.Type.Level.LevelExprSimplify02

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Type.Level.LevelExprSimplify` (part 2 of 7).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_denote_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_comm

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_assoc

#assert_no_axioms FX1Poly.Universe.LevelExpr.levelMax_succ_distrib

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_denote_comm

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_denote_assoc

#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_lmax_distrib_denote

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv.refl

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv.symm

#assert_no_axioms FX1Poly.Universe.LevelExpr.denoteEquiv.trans

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_comm_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_assoc_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_lmax_distrib_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_idempotent_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_lzero_left_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_lzero_right_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.simplify_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.lsucc_denoteEquiv_congr

#assert_no_axioms FX1Poly.Universe.LevelExpr.lmax_denoteEquiv_congr

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denoteEquiv_congr

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denote_lzero_right

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denote_lzero_left

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_denote_eq_lmax_when_codomain_nonzero

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_lzero_right_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.limax_lzero_left_denoteEquiv

#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat

#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_refl

#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_swap

#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_lt_trans

#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_gt_trans

#assert_no_axioms FX1Poly.Universe.LevelExpr.ctorIndex

#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen

#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_eq_of_both

#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_eq_inv

#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_swap

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_refl

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_swap

#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_eq_imp_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.compareNat_eq_iff_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_eq_imp_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_eq_iff_eq

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_cross_ctor

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_imp_ctorIndex_not_gt

#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_lt_iff

#assert_no_axioms FX1Poly.Universe.LevelExpr.orderingThen_eq_gt_iff

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_of_ctorIndex_lt

#assert_no_axioms FX1Poly.Universe.LevelExpr.compare_lt_trans_step

end FX1PolyAudit
