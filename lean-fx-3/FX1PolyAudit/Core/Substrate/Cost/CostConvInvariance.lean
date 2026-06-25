import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Cost.CostConvInvariance

/-! # FX1PolyAudit.Core.Substrate.Cost.CostConvInvariance — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepStarN.eq_of_zero
#assert_no_axioms FX1Poly.Core.StepStarN.eq_zero_of_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost_eq_zero_of_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.isStepNormalForm_of_normalizeCost_eq_zero
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost_eq_zero_iff_isStepNormalForm
#assert_no_axioms FX1Poly.Core.identityBetaFixture_normalizeCost_ne_zero
#assert_no_axioms FX1Poly.Core.costIsNotConvInvariant

end FX1PolyAudit
