import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableHeadExpansion

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableHeadExpansion

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableHeadExpansion`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.StepOverTableChildren.successorOver

#assert_no_axioms FX1Poly.Core.accOfTableStepClosure

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_toFireAtRootAtCell

#assert_no_axioms FX1Poly.Core.WfIotaTable.tableRedexHeadExpansion

#assert_no_axioms FX1Poly.Core.StepOverTableChildren.accNil

#assert_no_axioms FX1Poly.Core.StepOverTableChildren.accCons

#assert_no_axioms FX1Poly.Core.StepTable.tableRedexHeadExpansion

end FX1PolyAudit
