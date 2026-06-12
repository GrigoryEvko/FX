import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaTableStability

/-! # FX1PolyAudit/AuditEtaTableStability — ETA-T5 inc-4.3b shard

Per-declaration zero-axiom gate for the eta-stability induction: the
body-weakening transports, the full pair diagonal, the ★ three-way
mutual over the template grammar, and the depth-0 / firing-level
corollaries.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Transports and the pair diagonal -/

#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.weakenBodyUnderOneBinderBy
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.weakenBodyUnderTwoBindersBy
#assert_no_axioms FX1Poly.Core.StepEtaOverTableStar.substPair_diagonal

/-! ## ★ The mutual stability induction -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_etaStable
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_etaStable
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_etaStable

/-! ## Corollaries -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?_etaStable
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_etaStable

end FX1PolyAudit
