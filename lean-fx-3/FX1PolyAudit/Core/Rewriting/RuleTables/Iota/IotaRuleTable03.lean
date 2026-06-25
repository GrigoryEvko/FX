import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaRuleTable03

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable` (part 3 of 3).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

#assert_no_axioms FX1Poly.Core.multiScrutineeBoolIdDemoRule

#assert_no_axioms FX1Poly.Core.multiScrutineeBoolIdDemoRule_firesOnDistinctBools

#assert_no_axioms FX1Poly.Core.multiScrutineeBoolIdDemoRule_rejectsMatchingBools

#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule

#assert_no_axioms FX1Poly.Core.univalenceShapedDemoRule_firesOnUniverse

#assert_no_axioms FX1Poly.Core.guardedRejectDemoRule

#assert_no_axioms FX1Poly.Core.guardedRejectDemoRule_rejects

#assert_no_axioms FX1Poly.Core.rebuildUniversePayloadDemoRule

#assert_no_axioms FX1Poly.Core.rebuildUniversePayloadDemoRule_interpretsTarget

#assert_no_axioms FX1Poly.Core.nonStructuralReassemblyDemoRule

#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_isStructurallyRecursive

#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_isStructurallyRecursive

#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_isStructurallyRecursive

#assert_no_axioms FX1Poly.Core.nonStructuralReassemblyDemoRule_isNotStructurallyRecursive

#assert_no_axioms FX1Poly.Core.betaIotaRow_firesOnLamHeaded

#assert_no_axioms FX1Poly.Core.betaIotaRow_rejectsUnitHeaded

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow

#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow

#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow_interpretsTarget

#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow_interpretsTarget

#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow_interpretsTarget

end FX1PolyAudit
