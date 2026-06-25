import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Step.OneStepReductsComplete

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.OneStepReductsComplete — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.oneStepReducts_complete
#assert_no_axioms FX1Poly.Core.RawTermChildren.oneStepChildrenReducts_complete
#assert_no_axioms FX1Poly.Core.RawTerm.step_iff_mem_oneStepReducts

end FX1PolyAudit
