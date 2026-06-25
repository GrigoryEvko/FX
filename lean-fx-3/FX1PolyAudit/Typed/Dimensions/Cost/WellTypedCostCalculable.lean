import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Cost.WellTypedCostCalculable

/-! # FX1PolyAudit.Typed.Dimensions.Cost.WellTypedCostCalculable — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.costCalculator
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.costCalculator_isSound
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.canonicalEvaluationCost
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.canonicalEvaluationCost_isExact
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.canonicalEvaluationCost_le_costCalculator
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.costCalculatorOpen
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.costCalculatorOpen_isSound
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.canonicalEvaluationCostOpen
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.canonicalEvaluationCostOpen_isExact
#assert_no_axioms FX1Poly.Typed.wellTypedClosedProgram_costIsCalculable
#assert_no_axioms FX1Poly.Typed.identityApplication_costCalculator_isPositive

end FX1PolyAudit
