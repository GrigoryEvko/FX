import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Normalize.NormalizeCost

/-! # FX1PolyAudit.Core.Rewriting.Normalize.NormalizeCost — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_unfold
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_isExactChain
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_reducesToFst
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_fst_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeWithCost_fst_eq_normalize
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost_isExact
#assert_no_axioms FX1Poly.Core.unitNormalFormFixture
#assert_no_axioms FX1Poly.Core.unitNormalFormFixture_reduceOnce_halts
#assert_no_axioms FX1Poly.Core.unitNormalFormFixture_accessible
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost_unit_isZero

end FX1PolyAudit
