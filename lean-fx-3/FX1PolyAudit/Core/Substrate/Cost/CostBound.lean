import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Cost.CostBound

/-! # FX1PolyAudit.Core.Substrate.Cost.CostBound — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.costBoundOverReducts
#assert_no_axioms FX1Poly.Core.RawTerm.costBoundOverReducts_boundsElement
#assert_no_axioms FX1Poly.Core.RawTerm.costBound
#assert_no_axioms FX1Poly.Core.RawTerm.costBound_isSound
#assert_no_axioms FX1Poly.Core.RawTerm.normalizeCost_le_costBound
#assert_no_axioms FX1Poly.Core.RawTerm.costBound_unit_isZero
#assert_no_axioms FX1Poly.Core.identityBetaFixture_stepsToUnit
#assert_no_axioms FX1Poly.Core.identityBetaFixture_accessible
#assert_no_axioms FX1Poly.Core.identityBetaFixture_costBound_isPositive

end FX1PolyAudit
