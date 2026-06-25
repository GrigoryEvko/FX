import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Cost.SpaceBound

/-! # FX1PolyAudit.Core.Substrate.Cost.SpaceBound — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.OnCanonicalPath
#assert_no_axioms FX1Poly.Core.RawTerm.OnCanonicalPath.toStepStar
#assert_no_axioms FX1Poly.Core.RawTerm.spaceBound
#assert_no_axioms FX1Poly.Core.RawTerm.spaceBound_isSound
#assert_no_axioms FX1Poly.Core.RawTerm.size_le_spaceBound
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_onCanonicalPath
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_size_le_spaceBound
#assert_no_axioms FX1Poly.Core.RawTerm.spaceBound_unit_isOne
#assert_no_axioms FX1Poly.Core.identityBetaFixture_canonicalPathReachesUnit
#assert_no_axioms FX1Poly.Core.identityBetaFixture_spaceBound_boundsBothEndpoints

end FX1PolyAudit
