import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTableRenameReflection

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.StepOver.StepTableRenameReflection

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTableRenameReflection`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.scrutineeSlotLookup_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_reflectRename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire_reflectRename

#assert_no_axioms FX1Poly.Core.RawTerm.scopedChildrenView_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeChildrenAt?_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.elimPayloadAtDepth?_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?_rename

#assert_no_axioms FX1Poly.Core.scopedChildAt?_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_rename_none

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_rename_none

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_rename_none

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?_rename

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_rename

#assert_no_axioms FX1Poly.Core.StepOverTable.reflectRename

end FX1PolyAudit
