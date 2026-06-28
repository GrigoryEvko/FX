import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Graded.AppScaledSubstMetatheory

/-! # FX1PolyAudit.Typed.Dimensions.Graded.AppScaledSubstMetatheory — zero-axiom gate (mirror shard)

The per-declaration `#assert_no_axioms` gate for the App-scaled substitution metatheory: the
grade-arithmetic helpers, the `gen_app` reassociation heart, the sub-grade child-monotonicity, the
binder-former cell-grade equations, the head-scalar substitution-monotonicity, the substitution-master
statement, and the root-redex obligations (β / endpoint-β / a selection-row representative). -/

namespace FX1PolyAudit

-- Grade-arithmetic helpers + the gen_app reassociation heart
#assert_no_axioms FX1Poly.Typed.UsageGrade.le_add_right
#assert_no_axioms FX1Poly.Typed.UsageGrade.le_add_left
#assert_no_axioms FX1Poly.Typed.UsageGrade.addExchangeFourWay
#assert_no_axioms FX1Poly.Typed.appScaledAppNodeReassoc

-- Sub-grade child-monotonicity (the selection-row fact)
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appScaledDimensionGradeFold_head_le
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appScaledDimensionGradeFold_tail_le

-- Binder-former cell-grade equations
#assert_no_axioms FX1Poly.Typed.appScaled_lamCell
#assert_no_axioms FX1Poly.Typed.appScaled_pathLamCell
#assert_no_axioms FX1Poly.Typed.appScaled_pathAppCell
#assert_no_axioms FX1Poly.Typed.appScaled_pairCell
#assert_no_axioms FX1Poly.Typed.functionBinderGrade_lamCell

-- The head-scalar is substitution-non-increasing (the App-case ingredient)
#assert_no_axioms FX1Poly.Typed.RawTerm.functionBinderGrade_subst_le

-- The substitution master (statement) + its loose corollary + the root-redex obligations
#assert_no_axioms FX1Poly.Typed.IsAppScaledSubst0Bounded
#assert_no_axioms FX1Poly.Typed.appScaledDimensionGrade_subst0_looseBound
#assert_no_axioms FX1Poly.Typed.appScaledRootBeta_le
#assert_no_axioms FX1Poly.Typed.appScaledRootPathBeta_le_ofAffine
#assert_no_axioms FX1Poly.Typed.appScaledRootFstPair_le

-- ★ The discharge route: the App-scaled rename-image, the weaken-succ corollary, the substitution
-- profile + its binder transport, the App-scaled substitution master, and the singleton-profile
-- specialisation that discharges IsAppScaledSubst0Bounded.
#assert_no_axioms FX1Poly.Typed.UsageGrade.zero_le
#assert_no_axioms FX1Poly.Typed.RawTerm.functionBinderGrade_rename
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_appCell
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appScaledDimensionGrade_rename_childrenBound
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_rename_image_fueled
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_rename_image
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_weaken_succ
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_var_self
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_var_of_ne
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_var_succ
#assert_no_axioms FX1Poly.Typed.RawTermSubst.appScaledHitsWithWeight
#assert_no_axioms FX1Poly.Typed.RawTermSubst.lift_appScaledHitsWithWeight_succ
#assert_no_axioms FX1Poly.Typed.iterateLift_appScaledHitsWithWeight_raised
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appScaledDimensionGrade_subst_childrenBound
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_subst_weightProfile_fueled
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_subst_weightProfile
#assert_no_axioms FX1Poly.Typed.RawTermSubst.singleton_appScaledHitsWithWeight
#assert_no_axioms FX1Poly.Typed.isAppScaledSubst0Bounded_holds
#assert_no_axioms FX1Poly.Typed.appScaledDimensionGrade_subst0_bound
#assert_no_axioms FX1Poly.Typed.appScaledDimensionGrade_subst0_looseBound_unconditional
#assert_no_axioms FX1Poly.Typed.appScaledRootBeta_le_unconditional
#assert_no_axioms FX1Poly.Typed.appScaledRootPathBeta_le_ofAffine_unconditional

end FX1PolyAudit
