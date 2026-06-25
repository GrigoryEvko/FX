import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Normalizer.NormalizeStepsTower

/-! # FX1PolyAudit.Typed.Metatheory.Normalizer.NormalizeStepsTower — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.RawTerm.reduceOnce_idTower_succ
#assert_no_axioms FX1Poly.Typed.RawTerm.reduceOnce_idTower_zero
#assert_no_axioms FX1Poly.Typed.normalizeSteps_idTower
#assert_no_axioms FX1Poly.Typed.normalizeSteps_unbounded
#assert_no_axioms FX1Poly.Typed.idTower_normalizeChainExact
#assert_no_axioms FX1Poly.Typed.convDecideSteps_idTower
#assert_no_axioms FX1Poly.Typed.convDecideSteps_unbounded

end FX1PolyAudit
