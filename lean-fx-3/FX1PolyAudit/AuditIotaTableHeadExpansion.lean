import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableHeadExpansion

/-! # FX1PolyAudit/AuditIotaTableHeadExpansion — IOTA-T8 Tier-3 audit shard

Per-declaration zero-axiom gate for the children-spine successor order,
the accessibility transports, the firing cell-transport seam, the ★
generic table head-expansion arm at the SN candidate, the spine
accessibility composition bricks, and the ★★ canonical 18-row
instantiation.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Successor order + accessibility transport -/

#assert_no_axioms FX1Poly.Core.StepOverTableChildren.successorOver
#assert_no_axioms FX1Poly.Core.accOfTableStepClosure

/-! ## The firing cell-transport seam -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_toFireAtRootAtCell

/-! ## ★ The generic head-expansion arm at the SN candidate -/

#assert_no_axioms FX1Poly.Core.WfIotaTable.tableRedexHeadExpansion

/-! ## Spine accessibility composition -/

#assert_no_axioms FX1Poly.Core.StepOverTableChildren.accNil
#assert_no_axioms FX1Poly.Core.StepOverTableChildren.accCons

/-! ## ★★ The canonical 18-row instantiation -/

#assert_no_axioms FX1Poly.Core.StepTable.tableRedexHeadExpansion

end FX1PolyAudit
