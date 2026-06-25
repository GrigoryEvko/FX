import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.IsTypeDesc.IsTypeDescGenericSmoke

/-! # FX1PolyAudit.Typed.Engine.IsTypeDesc.IsTypeDescGenericSmoke — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.IsTypeDesc.decidesAsTypeBool
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_universeCode
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_pi
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_sigma
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_nestedPi
#assert_no_axioms FX1Poly.Typed.decideTypeGeneric_smoke_emptyCodeDeferred

end FX1PolyAudit
