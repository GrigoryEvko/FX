import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableFireRoot

/-! # FX1PolyAudit/AuditTableFireRoot — IOTA-T4 audit shard (generic root firing)

Per-declaration zero-axiom gate for the table-driven root firing that
replaces the twelve-deep `dite`-chains of `fireRootRedex` /
`hasRootStepSource`: the per-row firing + its soundness and
head-detection, the table walk + ONE soundness and ONE completeness,
the detection predicates, and the canonical-table instantiations with
the kernel-`Step` bridge over the legacy 17 rows.  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Per-row firing -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_sound
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.detectsHeadAtRoot
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_isSome_imp_detectsHeadAtRoot

/-! ## The table walk + soundness/completeness -/

#assert_no_axioms FX1Poly.Core.fireTableRedexOver
#assert_no_axioms FX1Poly.Core.fireTableRedexOver_sound
#assert_no_axioms FX1Poly.Core.fireTableRedexOver_complete
#assert_no_axioms FX1Poly.Core.hasTableRedexRootOver
#assert_no_axioms FX1Poly.Core.detectsHeadRedexRootOver
#assert_no_axioms FX1Poly.Core.fireTableRedexOver_isSome_imp_headDetected

/-! ## The canonical 18-row instantiation + the legacy Step bridge -/

#assert_no_axioms FX1Poly.Core.StepTable.fireRoot
#assert_no_axioms FX1Poly.Core.StepTable.fireRoot_sound
#assert_no_axioms FX1Poly.Core.StepTable.hasRedexRoot
#assert_no_axioms FX1Poly.Core.StepTable.detectsHeadRoot
#assert_no_axioms FX1Poly.Core.StepTable.fireRoot_isSome_imp_detectsHeadRoot
#assert_no_axioms FX1Poly.Core.StepTable.fireRootLegacy
#assert_no_axioms FX1Poly.Core.StepTable.fireRootLegacy_imp_step

end FX1PolyAudit
