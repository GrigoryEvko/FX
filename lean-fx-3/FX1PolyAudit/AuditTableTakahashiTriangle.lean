import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableTakahashiTriangle

/-! # FX1PolyAudit/AuditTableTakahashiTriangle — IOTA-T6 audit shard (the finale)

Per-declaration zero-axiom gate for the complete development, its walk
lemmas, the development parallel step, the ★ Takahashi triangle, the
parallel diamond, and table confluence — including the ★★ canonical
18-row instantiation.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## The split-firing root walk -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireSplitAtRoot?
#assert_no_axioms FX1Poly.Core.fireSplitTableRedexOver
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireSplitAtRoot?_someInversion
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireSplitAtRoot?_firesAtDevelopedRoot
#assert_no_axioms FX1Poly.Core.fireSplitTableRedexOver_someInversion
#assert_no_axioms FX1Poly.Core.WfIotaTable.fireSplitTableRedexOver_eq_ofRowFires

/-! ## Complete development -/

#assert_no_axioms FX1Poly.Core.completeDevelopOverTable
#assert_no_axioms FX1Poly.Core.completeDevelopChildrenOverTable
#assert_no_axioms FX1Poly.Core.ParStepOverTable.toCompleteDevelopment
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.toCompleteDevelopment

/-! ## The triangle, diamond, confluence -/

#assert_no_axioms FX1Poly.Core.ParStepOverTable.triangle
#assert_no_axioms FX1Poly.Core.ParStepOverTableChildren.triangleChildren
#assert_no_axioms FX1Poly.Core.ParStepOverTable.diamond
#assert_no_axioms FX1Poly.Core.StepOverTable.confluent
#assert_no_axioms FX1Poly.Core.StepTable.confluent

end FX1PolyAudit
