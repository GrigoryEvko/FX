import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTableEquivariance

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.StepOver.StepTableEquivariance

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTableEquivariance`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.iotaRuleTable_isScopeUniform

#assert_no_axioms FX1Poly.Core.betaIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.boolFalseIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.fstPairIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.sndPairIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.listElimNilIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.idJReflIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_isScopeUniform

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.interpretTarget?_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineesFire_subst

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_subst

#assert_no_axioms FX1Poly.Core.StepOverTable.subst

#assert_no_axioms FX1Poly.Core.StepOverTableChildren.subst

#assert_no_axioms FX1Poly.Core.StepTable.subst

#assert_no_axioms FX1Poly.Core.StepOverTable.rename

#assert_no_axioms FX1Poly.Core.StepTable.rename

end FX1PolyAudit
