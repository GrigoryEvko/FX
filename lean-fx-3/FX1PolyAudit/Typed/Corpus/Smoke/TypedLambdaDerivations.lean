import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Corpus.Smoke.TypedLambdaDerivations

/-! # FX1PolyAudit.Typed.Corpus.Smoke.TypedLambdaDerivations — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.genFormationPiTypesBothPiAndSigmaFormers
#assert_no_axioms FX1Poly.Typed.identityLambdaViaIntroTable
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables
#assert_no_axioms FX1Poly.Typed.ruleTableApplicationOutput_resolvesToUniverse
#assert_no_axioms FX1Poly.Typed.identityApplicationViaRuleTables_atResolvedType

end FX1PolyAudit
