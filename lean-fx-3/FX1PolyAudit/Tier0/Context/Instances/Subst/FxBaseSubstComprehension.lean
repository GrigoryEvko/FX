import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstComprehension

/-! # FX1PolyAudit.Tier0.Context.Instances.Subst.FxBaseSubstComprehension — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.SubstVec.cons
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_lookup_zero
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_lookup_succ
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_compose_cons
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_toRawTermSubst
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_unique

end FX1PolyAudit
