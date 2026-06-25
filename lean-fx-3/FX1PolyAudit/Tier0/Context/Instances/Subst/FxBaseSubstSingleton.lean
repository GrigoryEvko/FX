import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstSingleton

/-! # FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstSingleton — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton
#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton_lookup_zero
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_compose_singleton
#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton_toRawTermSubst
#assert_no_axioms FX1Poly.Tier0.SubstVec.subst_singleton_eq_subst0

end FX1PolyAudit
