import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaRuleTable02

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable` (part 2 of 3).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_typedOutputInterprets

#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_typedOutputInterprets

#assert_no_axioms FX1Poly.Core.idJReflIotaRow_typedOutputInterprets

#assert_no_axioms FX1Poly.Core.betaIotaRow_typedOutputAbsent

#assert_no_axioms FX1Poly.Core.scrutineeEchoDemoRule

end FX1PolyAudit
