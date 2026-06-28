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

end FX1PolyAudit
