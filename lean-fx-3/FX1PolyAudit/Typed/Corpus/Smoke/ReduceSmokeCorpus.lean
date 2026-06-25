import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Corpus.Smoke.ReduceSmokeCorpus

/-! # FX1PolyAudit.Typed.Corpus.Smoke.ReduceSmokeCorpus — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.reduceOnce_betaIdentity_fires
#assert_no_axioms FX1Poly.Typed.reduceOnce_betaConstant_fires
#assert_no_axioms FX1Poly.Typed.reduceOnce_identityLambda_halts
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_betaRedex_false
#assert_no_axioms FX1Poly.Typed.isStepNormalFormBool_identityLambda_true
#assert_no_axioms FX1Poly.Typed.fireTableRedex_betaIdentity_fires

end FX1PolyAudit
