import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Cost.CostAwareEquivalence

/-! # FX1PolyAudit.Typed.Dimensions.Cost.CostAwareEquivalence — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.Improves
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.Improves.refl
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.Improves.trans
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv.refl
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv.sym
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv.trans
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv.costEq
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv.improves
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv.improvesReverse
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.CostEquiv.ofImprovesBoth
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalFormDerivation
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalFormDerivation_cost_isZero
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalFormDerivation_improves
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.normalFormDerivation_improvesAllConvertible
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decideImproves
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.decideCostEquiv
#assert_no_axioms FX1Poly.Typed.identityApplicationRedexDerivation
#assert_no_axioms FX1Poly.Typed.identityApplicationReductDerivation
#assert_no_axioms FX1Poly.Typed.identityApplicationReduct_isStepNormalForm
#assert_no_axioms FX1Poly.Typed.identityApplicationReduct_strictlyImproves

end FX1PolyAudit
