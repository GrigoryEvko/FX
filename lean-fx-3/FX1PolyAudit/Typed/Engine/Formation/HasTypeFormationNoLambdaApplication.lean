import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Formation.HasTypeFormationNoLambdaApplication

/-! # FX1PolyAudit.Typed.Engine.Formation.HasTypeFormationNoLambdaApplication — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeLambda
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectCannotBeApplication
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_lam
#assert_no_axioms FX1Poly.Typed.HasTypeDesc.subjectRootGenerator_ne_app

end FX1PolyAudit
