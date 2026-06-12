import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaIotaScrutineeDichotomy

/-! # FX1PolyAudit/AuditEtaIotaScrutineeDichotomy — ETA-T5 inc-4.4b shard

Per-declaration zero-axiom gate for the cong-eta/iota case split: the
per-spec good/duality disjunction (freed-subject step inversion), the
membership fold, the backward `scrutineesFire` rebuild, and the ★
row-level dichotomy producing the full backward-firing hypotheses or
the duality witness.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The per-spec analysis -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_etaDisjunction

/-! ## The folds -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire_ofMemberFires
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeList_etaDisjunction

/-! ## ★ The row-level dichotomy -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineePattern_etaDichotomy

end FX1PolyAudit
