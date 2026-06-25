import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaRuleTable01

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable` (part 1 of 3).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.ScopedChild

#assert_no_axioms FX1Poly.Core.RawTermChildren.toScopedChildren

#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftZero?

#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftOne?

#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftTwo?

#assert_no_axioms FX1Poly.Core.listEntryAt?

#assert_no_axioms FX1Poly.Core.scopedChildAt?

#assert_no_axioms FX1Poly.Core.RawTerm.scopedChildrenView

#assert_no_axioms FX1Poly.Core.natListLookup?

#assert_no_axioms FX1Poly.Core.natListContains

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBy

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderOneBinderBy

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderTwoBindersBy

#assert_no_axioms FX1Poly.Core.RawTermChildren.weakenSpineBy

#assert_no_axioms FX1Poly.Core.replacementIntoShift?

#assert_no_axioms FX1Poly.Core.RawTermChildren.replaceChildAt?

#assert_no_axioms FX1Poly.Core.ScrutineeSpec

#assert_no_axioms FX1Poly.Core.PayloadSource

#assert_no_axioms FX1Poly.Core.ReductTemplate

#assert_no_axioms FX1Poly.Core.ReductTemplateSpine

#assert_no_axioms FX1Poly.Core.SpineReplacements

#assert_no_axioms FX1Poly.Core.IotaRuleDesc

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecAt?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSlots

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.motiveBinderArity?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSlotShift?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermAt?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeChildrenAt?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermOf?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeChildrenOf?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.elimPayloadAtDepth?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.resolvePayloadSource?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTypedOutput?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?

#assert_no_axioms FX1Poly.Core.ReductTemplate.isScrutineeChildProjection

#assert_no_axioms FX1Poly.Core.ReductTemplate.hasOnlyStructuralReassemblies

#assert_no_axioms FX1Poly.Core.ReductTemplateSpine.hasOnlyStructuralReassemblies

#assert_no_axioms FX1Poly.Core.SpineReplacements.areStructuralOver

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.isStructurallyRecursive

#assert_no_axioms FX1Poly.Core.betaIotaRow

#assert_no_axioms FX1Poly.Core.boolTrueIotaRow

#assert_no_axioms FX1Poly.Core.boolFalseIotaRow

#assert_no_axioms FX1Poly.Core.fstPairIotaRow

end FX1PolyAudit
