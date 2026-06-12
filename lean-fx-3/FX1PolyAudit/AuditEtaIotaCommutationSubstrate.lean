import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaIotaCommutationSubstrate

/-! # FX1PolyAudit/AuditEtaIotaCommutationSubstrate — ETA-T5 inc-1 shard

Per-declaration zero-axiom gate for the positional-step workhorse of
the eta/iota quasi-commutation.  Must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepOverTableChildren.ofChildAtShiftStep

end FX1PolyAudit
