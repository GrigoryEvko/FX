import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaRuleTable

/-! # FX1PolyAudit/AuditIotaRuleTable — IOTA-T0 audit shard (the ι-rule table spike)

Per-declaration zero-axiom gate for the IOTA-TABLE design spike: the shift-erased child view, the
depth-weakening helpers (rfl-at-depth-0), the cast-free slot replacement, the closed reduct-template DSL
(`ReductTemplate`/`SpineReplacements`), the dependent-wired rule descriptor (`IotaRuleDesc` with
`motiveSlot?` + derived `motiveBinderArity?`), the depth-graded template interpreter with derived
scrutinee, the firing dispatcher, all 18 rows, the 18 `rfl` adequacy equations (the GO gate), the
dependent-wiring pins, and the new-node demo equations (motive instantiation, whole-scrutinee echo,
two-binder scrutinee substitution, multi-slot reassembly, the W-style under-binder recursion, path-binder
wrapping, firing positive + negative).  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The shift-erased child view -/

#assert_no_axioms FX1Poly.Core.ScopedChild
#assert_no_axioms FX1Poly.Core.RawTermChildren.toScopedChildren
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftZero?
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftOne?
#assert_no_axioms FX1Poly.Core.ScopedChild.atShiftTwo?
#assert_no_axioms FX1Poly.Core.scopedChildAt?
#assert_no_axioms FX1Poly.Core.RawTerm.scopedChildrenView
#assert_no_axioms FX1Poly.Core.natListLookup?

/-! ## Depth weakening + cast-free slot replacement -/

#assert_no_axioms FX1Poly.Core.RawTerm.weakenBy
#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderOneBinderBy
#assert_no_axioms FX1Poly.Core.RawTerm.weakenBodyUnderTwoBindersBy
#assert_no_axioms FX1Poly.Core.RawTermChildren.weakenSpineBy
#assert_no_axioms FX1Poly.Core.replacementIntoShift?
#assert_no_axioms FX1Poly.Core.RawTermChildren.replaceChildAt?

/-! ## The DSL, the descriptor, the interpreter -/

#assert_no_axioms FX1Poly.Core.ReductTemplate
#assert_no_axioms FX1Poly.Core.SpineReplacements
#assert_no_axioms FX1Poly.Core.IotaRuleDesc
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.motiveBinderArity?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSlotShift?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeTermOf?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeChildrenOf?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.elimPayloadAtDepth?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?

/-! ## The 18 rows + the table -/

#assert_no_axioms FX1Poly.Core.betaIotaRow
#assert_no_axioms FX1Poly.Core.boolTrueIotaRow
#assert_no_axioms FX1Poly.Core.boolFalseIotaRow
#assert_no_axioms FX1Poly.Core.fstPairIotaRow
#assert_no_axioms FX1Poly.Core.sndPairIotaRow
#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow
#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow
#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow
#assert_no_axioms FX1Poly.Core.listElimNilIotaRow
#assert_no_axioms FX1Poly.Core.listElimConsIotaRow
#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow
#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow
#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow
#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow
#assert_no_axioms FX1Poly.Core.idJReflIotaRow
#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow
#assert_no_axioms FX1Poly.Core.pathBetaIotaRow
#assert_no_axioms FX1Poly.Core.iotaRuleTable
#assert_no_axioms FX1Poly.Core.iotaRuleTable_length

/-! ## The 18 adequacy equations (the GO gate) -/

#assert_no_axioms FX1Poly.Core.betaIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.boolFalseIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.fstPairIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.sndPairIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.listElimNilIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.idJReflIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_interpretsTarget
#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_interpretsTarget

/-! ## Dependent-wiring pins -/

#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_motiveArity
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_motiveArity
#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_motiveArity
#assert_no_axioms FX1Poly.Core.idJReflIotaRow_motiveArity
#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_motiveArity
#assert_no_axioms FX1Poly.Core.betaIotaRow_motiveArity
#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_motiveArity
#assert_no_axioms FX1Poly.Core.betaIotaRow_scrutineeShift
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_scrutineeShift
#assert_no_axioms FX1Poly.Core.idJReflIotaRow_scrutineeShift

/-! ## New-node demo rules + demo adequacy equations -/

#assert_no_axioms FX1Poly.Core.scrutineeEchoDemoRule
#assert_no_axioms FX1Poly.Core.scrutineeEchoDemoRule_interpretsTarget
#assert_no_axioms FX1Poly.Core.natElimMotiveAtScrutineeDemoRule
#assert_no_axioms FX1Poly.Core.natElimMotiveAtScrutineeDemoRule_interpretsTarget
#assert_no_axioms FX1Poly.Core.idJMotivePairDemoRule
#assert_no_axioms FX1Poly.Core.idJMotivePairDemoRule_interpretsTarget
#assert_no_axioms FX1Poly.Core.scrutineeTwoBinderSubstDemoRule
#assert_no_axioms FX1Poly.Core.scrutineeTwoBinderSubstDemoRule_interpretsTarget
#assert_no_axioms FX1Poly.Core.natElimMultiSlotReassemblyDemoRule
#assert_no_axioms FX1Poly.Core.natElimMultiSlotReassemblyDemoRule_interpretsTarget
#assert_no_axioms FX1Poly.Core.wStyleRecursiveBinderDemoRule
#assert_no_axioms FX1Poly.Core.wStyleRecursiveBinderDemoRule_interpretsTarget
#assert_no_axioms FX1Poly.Core.pathBinderEchoDemoRule
#assert_no_axioms FX1Poly.Core.pathBinderEchoDemoRule_interpretsTarget

/-! ## Firing dispatcher smoke -/

#assert_no_axioms FX1Poly.Core.betaIotaRow_firesOnLamHeaded
#assert_no_axioms FX1Poly.Core.betaIotaRow_rejectsUnitHeaded

end FX1PolyAudit
