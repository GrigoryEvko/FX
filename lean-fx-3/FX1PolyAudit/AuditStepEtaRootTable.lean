import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepEtaRootTable

/-! # FX1PolyAudit/AuditStepEtaRootTable — ETA-T6 inc-5a shard

Per-declaration zero-axiom gate for the root-only table eta tier: the
relation, its embedding into the full table eta, the freed-subject
inversion, and the ★ determinism under the distinct-roots
certificate.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepEtaRootOverTable
#assert_no_axioms FX1Poly.Core.StepEtaRootOverTable.toStepEtaOverTable
#assert_no_axioms FX1Poly.Core.StepEtaRootOverTable.invert
#assert_no_axioms FX1Poly.Core.StepEtaRootOverTable.deterministic

end FX1PolyAudit
