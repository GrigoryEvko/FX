import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableStructuralSR

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableStructuralSR

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableStructuralSR`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.HasSortCertifiedTarget

#assert_no_axioms FX1Poly.Core.optionBindSomeSplit

#assert_no_axioms FX1Poly.Core.optionMapSomeSplit

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_ofIndex

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTemplate?_certified

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretBuiltChildren?_certified

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretReplacements?_certified

#assert_no_axioms FX1Poly.Core.HasCertifiedCellDim0.preservedByTableRedex

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.HasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.hasSortCertifiedTarget_ofPreserving

#assert_no_axioms FX1Poly.Core.betaIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.boolFalseIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.fstPairIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.sndPairIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.listElimNilIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.idJReflIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.PolyCell.preservedByTableRedex_dim0

#assert_no_axioms FX1Poly.Core.iotaRuleTable_hasSortPreservingTargets

#assert_no_axioms FX1Poly.Core.quotRecMkIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.quotElimMkIotaRow_hasSortPreservingTarget

#assert_no_axioms FX1Poly.Core.truncRecIntroIotaRow_hasSortPreservingTarget

end FX1PolyAudit
