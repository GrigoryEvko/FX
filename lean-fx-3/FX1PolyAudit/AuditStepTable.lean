import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepTable

/-! # FX1PolyAudit/AuditStepTable — IOTA-T1 audit shard (the table-driven reduction relation)

Per-declaration zero-axiom gate for IOTA-T1: the parameterized `StepOverTable` relation (the RW-5
keystone shape), the legacy 17-row table + its pins, table monotonicity, the 18 membership witnesses,
the FORWARD adequacy (`Step ⊆ StepOverTable legacyIotaRuleTable`, each root arm a `rfl` firing), the
generic firing-inversion trio, the 17 per-row root inversions, the BACKWARD adequacy, the headline
both-direction `stepOverLegacyTable_iff_step`, the canonical embedding `Step.toStepTable`, and the
honesty-ledger liveness of the table-native endpoint-β (`StepTable.pathBetaFires`).  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The tables + the relation -/

#assert_no_axioms FX1Poly.Core.legacyIotaRuleTable
#assert_no_axioms FX1Poly.Core.legacyIotaRuleTable_length
#assert_no_axioms FX1Poly.Core.iotaRuleTable_eq_legacyAppendPathBeta
#assert_no_axioms FX1Poly.Core.StepOverTable
#assert_no_axioms FX1Poly.Core.StepOverTableChildren
#assert_no_axioms FX1Poly.Core.StepTable

/-! ## Monotonicity -/

#assert_no_axioms FX1Poly.Core.listMemAppendLeft
#assert_no_axioms FX1Poly.Core.legacyRow_memFullTable
#assert_no_axioms FX1Poly.Core.StepOverTable.monotone
#assert_no_axioms FX1Poly.Core.StepOverTableChildren.monotone

/-! ## Membership witnesses -/

#assert_no_axioms FX1Poly.Core.betaIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.boolFalseIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.fstPairIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.sndPairIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.listElimNilIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.idJReflIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_memLegacy
#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_memTable

/-! ## FORWARD adequacy -/

#assert_no_axioms FX1Poly.Core.Step.toLegacyTableStep
#assert_no_axioms FX1Poly.Core.StepChildren.toLegacyTableStepChildren

/-! ## The generic firing-inversion trio -/

#assert_no_axioms FX1Poly.Core.andEqTrueSplit
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_some_scrutineesFire
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_extractsHead
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.firesOn?_some_primaryHead

/-! ## The 17 per-row root inversions -/

#assert_no_axioms FX1Poly.Core.betaRowFiringToHeadStep
#assert_no_axioms FX1Poly.Core.betaRowFiringToStep
#assert_no_axioms FX1Poly.Core.boolTrueRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.boolFalseRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.fstPairRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.sndPairRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.natElimZeroRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.natRecZeroRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.natElimSuccRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.natRecSuccRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.listElimNilRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.listElimConsRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.optionMatchNoneRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.optionMatchSomeRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.eitherMatchInlRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.eitherMatchInrRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.idJReflRowFiringToIotaHead
#assert_no_axioms FX1Poly.Core.idStrictRecReflRowFiringToIotaHead

/-! ## BACKWARD adequacy + the headline -/

#assert_no_axioms FX1Poly.Core.legacyRootFiringToStep
#assert_no_axioms FX1Poly.Core.legacyRootFiringToWeakHeadStep
#assert_no_axioms FX1Poly.Core.Step.childCongruenceOfElimHeadsExcluded
#assert_no_axioms FX1Poly.Core.StepOverTable.legacyToStep
#assert_no_axioms FX1Poly.Core.StepOverTableChildren.legacyToStepChildren
#assert_no_axioms FX1Poly.Core.stepOverLegacyTable_iff_step
#assert_no_axioms FX1Poly.Core.Step.toStepTable

/-! ## Honesty ledger: the table-native row is live -/

#assert_no_axioms FX1Poly.Core.StepTable.pathBetaFires

/-! ## The legacy fire-root bridge (lives with the adequacy layer) -/

#assert_no_axioms FX1Poly.Core.StepTable.fireRootLegacy_imp_step

end FX1PolyAudit
