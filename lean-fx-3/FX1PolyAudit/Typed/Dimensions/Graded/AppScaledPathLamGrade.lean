import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Graded.AppScaledPathLamGrade

/-! # FX1PolyAudit.Typed.Dimensions.Graded.AppScaledPathLamGrade — zero-axiom gate (mirror shard)

The per-declaration `#assert_no_axioms` gate for the App-SCALED beta-stable dimension-usage grade: the
grade-arithmetic helpers, the function-binder scalar + its `Step`-monotonicity, the table fact, the
recursive App-scaled grade (term + two spine companions) with its unfolding equations, the root-redex
obligation, and the congruence-half preservation (fuel-bounded form + the size-bounded spine engine +
the size-instantiated wrapper). -/

namespace FX1PolyAudit

-- Grade-arithmetic combinators
#assert_no_axioms FX1Poly.Typed.UsageGrade.le_omega
#assert_no_axioms FX1Poly.Typed.UsageGrade.mul_le_mul

-- The App rule's scalar + the table fact
#assert_no_axioms FX1Poly.Typed.RawTerm.functionBinderGrade
#assert_no_axioms FX1Poly.Typed.RawTerm.functionBinderGrade_mkGen
#assert_no_axioms FX1Poly.Typed.iotaRuleTable_elimGenerator_ne_pathLam

-- The recursive App-scaled dimension grade (term + spine companions) + unfolding equations
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appScaledDimensionGradeFold
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appHeadScaledDimensionGrade
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_mkGen
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_nonApp
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_app
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appScaledDimensionGradeFold_childCons
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appHeadScaledDimensionGrade_childCons

-- The function-binder scalar never increases under a Step
#assert_no_axioms FX1Poly.Typed.RawTerm.functionBinderGrade_step_monotone

-- The root obligation + the congruence-half preservation
#assert_no_axioms FX1Poly.Typed.AppScaledRootRedexPreserved
#assert_no_axioms FX1Poly.Typed.RawTermChildren.appScaledDimensionGrade_stepChildren_le_ofTermBound
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_step_le_ofRootPreserved_fueled
#assert_no_axioms FX1Poly.Typed.RawTerm.appScaledDimensionGrade_step_le_of_rootPreserved

end FX1PolyAudit
