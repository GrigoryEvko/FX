import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.StaticTypingSoundness

/-! # FX1PolyAudit.Typed.Engine.Classifier.StaticTypingSoundness — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.orEqFalse_leftFalse
#assert_no_axioms FX1Poly.Typed.orEqFalse_rightFalse
#assert_no_axioms FX1Poly.Typed.notEqTrue_ofEqFalse
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_false_imp_isUntypableHead
#assert_no_axioms FX1Poly.Typed.grownReservedUntyped
#assert_no_axioms FX1Poly.Typed.reservedHeadUntypedBySurvivingEngines

end FX1PolyAudit
