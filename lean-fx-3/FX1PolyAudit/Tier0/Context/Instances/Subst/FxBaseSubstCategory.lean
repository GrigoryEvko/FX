import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstCategory

/-! # FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstCategory — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.SubstVec.identity
#assert_no_axioms FX1Poly.Tier0.SubstVec.identity_lookup
#assert_no_axioms FX1Poly.Tier0.SubstVec.compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.lookup_compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.identity_compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.compose_identity
#assert_no_axioms FX1Poly.Tier0.SubstVec.compose_assoc
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstCategory
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstCategory_identity_eq
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstCategory_compose_eq

end FX1PolyAudit
