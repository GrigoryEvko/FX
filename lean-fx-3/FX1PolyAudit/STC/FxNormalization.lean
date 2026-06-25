import FX1PolyAudit.DependencyAudit
import FX1Poly.STC.FxNormalization

/-! # FX1PolyAudit.STC.FxNormalization — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.STC.ReachesNormalForm
#assert_no_axioms FX1Poly.STC.fxStcNormalizationRelation
#assert_no_axioms FX1Poly.STC.normalizationViaSTC
#assert_no_axioms FX1Poly.STC.normalizationViaSTC_extracts
#assert_no_axioms FX1Poly.STC.normalizationViaSTC_semantic_isKernelWitness
#assert_no_axioms FX1Poly.STC.normalizationViaSTC_syntactic_eq
#assert_no_axioms FX1Poly.STC.identityApplicationClosedTyped
#assert_no_axioms FX1Poly.STC.normalizationViaSTC_betaRedex_nonVacuous

end FX1PolyAudit
