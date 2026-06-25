import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Step.OneStepReducts

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.OneStepReducts — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.oneStepReducts
#assert_no_axioms FX1Poly.Core.RawTermChildren.oneStepChildrenReducts
#assert_no_axioms FX1Poly.Core.RawTerm.oneStepReducts_sound
#assert_no_axioms FX1Poly.Core.RawTermChildren.oneStepChildrenReducts_sound
#assert_no_axioms FX1Poly.Core.identityBetaFixture
#assert_no_axioms FX1Poly.Core.identityBetaFixture_oneStepReducts

end FX1PolyAudit
