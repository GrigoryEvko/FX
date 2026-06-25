import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Step.ReduceOnceComplete

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.ReduceOnceComplete — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_complete
#assert_no_axioms FX1Poly.Core.RawTermChildren.reduceOnceSpine_complete
#assert_no_axioms FX1Poly.Core.RawTerm.reduceOnce_eq_none_iff_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.not_isStepNormalForm_imp_reduceOnce_isSome

end FX1PolyAudit
