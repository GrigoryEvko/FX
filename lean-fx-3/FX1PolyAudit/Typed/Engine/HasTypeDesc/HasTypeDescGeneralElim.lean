import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGeneralElim

/-! # FX1PolyAudit.Typed.Engine.HasTypeDesc.HasTypeDescGeneralElim — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.appGeneralElimRule
#assert_no_axioms FX1Poly.Typed.pathAppGeneralElimRule
#assert_no_axioms FX1Poly.Typed.generalElimRuleOf_app
#assert_no_axioms FX1Poly.Typed.generalElimRuleOf_pathApp
#assert_no_axioms FX1Poly.Typed.generalElimRuleOf_isAppOrPathApp
#assert_no_axioms FX1Poly.Typed.generalElimEngine_typesApp
#assert_no_axioms FX1Poly.Typed.generalElimEngine_typesPathApp
#assert_no_axioms FX1Poly.Typed.HasTypeDescGeneralElim.soundness
#assert_no_axioms FX1Poly.Typed.HasTypeDescGradedIntro.invertGeneric
#assert_no_axioms FX1Poly.Typed.gradedIntroEndpointIotaComputesTyped
#assert_no_axioms FX1Poly.Typed.closedApplicationGeneralElimTyped
#assert_no_axioms FX1Poly.Typed.neutralPathApplicationGeneralElimTyped
#assert_no_axioms FX1Poly.Typed.constantBridgeEndpointIotaSmoke
#assert_no_axioms FX1Poly.Typed.generalElimEngineCoverageWitness

end FX1PolyAudit
