import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Normalize.NormalizeMeta

/-! # FX1PolyAudit.Core.Rewriting.Normalize.NormalizeMeta — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.normalize_eq_self_of_isStepNormalForm
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_idempotent
#assert_no_axioms FX1Poly.Core.RawTerm.conv_normalize
#assert_no_axioms FX1Poly.Core.RawTerm.normalize_eq_iff_conv

end FX1PolyAudit
