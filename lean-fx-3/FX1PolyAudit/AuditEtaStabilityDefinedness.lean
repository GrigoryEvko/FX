import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaStabilityDefinedness

/-! # FX1PolyAudit/AuditEtaStabilityDefinedness — ETA-T5 inc-4.4a shard

Per-declaration zero-axiom gate for the backward definedness transfer:
the shape equi-definedness bricks (composed reads at every shift,
slot replacement), the source-side scrutinee-read pin, the ★ backward
success mutual over the template grammar, and the row-level
`firesOn?_etaReflected` corollary composing definedness with the
forward stability.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Shape equi-definedness bricks -/

#assert_no_axioms FX1Poly.Core.composedReadAtShiftZero_equiDefined
#assert_no_axioms FX1Poly.Core.composedReadAtShiftOne_equiDefined
#assert_no_axioms FX1Poly.Core.composedReadAtShiftTwo_equiDefined
#assert_no_axioms FX1Poly.Core.replaceChildAt?_equiDefined

/-! ## The source-side scrutinee pin -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?_ofFiring

/-! ## ★ The backward definedness mutual -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_definedTransfer
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?_definedTransfer
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_definedTransfer
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_definedTransfer

/-! ## Corollaries -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?_definedTransfer
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_etaReflected

end FX1PolyAudit
