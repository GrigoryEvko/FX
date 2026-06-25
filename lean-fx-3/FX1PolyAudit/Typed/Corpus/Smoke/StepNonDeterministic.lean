import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Corpus.Smoke.StepNonDeterministic

/-! # FX1PolyAudit.Typed.Corpus.Smoke.StepNonDeterministic — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.nondeterministicTerm_outerStep
#assert_no_axioms FX1Poly.Typed.nondeterministicTerm_innerStep
#assert_no_axioms FX1Poly.Typed.outerReduct_ne_innerReduct
#assert_no_axioms FX1Poly.Typed.outerReduct_reachesCommon
#assert_no_axioms FX1Poly.Typed.innerReduct_reachesCommon
#assert_no_axioms FX1Poly.Typed.stepIsNonDeterministicButDiamondCloses

end FX1PolyAudit
