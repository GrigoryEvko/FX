import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.KernelParamInternalVerdict

/-! # FX1PolyAudit/AuditKernelParamInternalVerdict — OP1-INT verdict audit shard

Per-declaration zero-axiom gate for the OP1-INT verdict: the refreshed endpoint-computation
ledger pin, the core-`Step` endpoint-β witness, and the GO-verdict bundle.  Free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.paramSubstrateLedger_endpointComputationLive
#assert_no_axioms FX1Poly.Typed.paramSubstrate_endpointBetaIsCoreStep
#assert_no_axioms FX1Poly.Typed.paramSubstrate_op1IntVerdictGo

end FX1PolyAudit
