import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrientedSN

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableOrientedSN01

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrientedSN` (part 1 of 2).
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.ReductTemplate.avoidsSubstitution

#assert_no_axioms FX1Poly.Core.ReductTemplateSpine.avoidsSubstitution

#assert_no_axioms FX1Poly.Core.SpineReplacements.avoidSubstitution

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.hasSubstitutionFreeReduct

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.isRpoOrientable

#assert_no_axioms FX1Poly.Core.boolTrueIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.boolFalseIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.fstPairIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.sndPairIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.natElimZeroIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.natRecZeroIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.listElimNilIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.listElimConsIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.optionMatchNoneIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.optionMatchSomeIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.eitherMatchInlIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.eitherMatchInrIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.idJReflIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.idStrictRecReflIotaRow_isRpoOrientable

#assert_no_axioms FX1Poly.Core.betaIotaRow_isNotRpoOrientable

#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_isNotRpoOrientable

#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_isNotRpoOrientable

#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_isNotRpoOrientable

#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_substitutes

#assert_no_axioms FX1Poly.Core.nonStructuralReassemblyDemoRule_avoidsSubstitution

#assert_no_axioms FX1Poly.Core.nonStructuralReassemblyDemoRule_isNotRpoOrientable

#assert_no_axioms FX1Poly.Core.iotaTableTierLedger

#assert_no_axioms FX1Poly.Core.iotaTableTierLedger_pinned

#assert_no_axioms FX1Poly.Core.orientedIotaRuleTable

#assert_no_axioms FX1Poly.Core.orientedIotaRuleTable_length

#assert_no_axioms FX1Poly.Core.orientedIotaRuleTable_eq_filter

#assert_no_axioms FX1Poly.Core.orientedRows_areRpoOrientable

#assert_no_axioms FX1Poly.Core.orientedRow_memFullTable

#assert_no_axioms FX1Poly.Core.boolTrueRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.boolFalseRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.fstPairRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.sndPairRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.natElimZeroRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.natRecZeroRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.listElimNilRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.listElimConsRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.optionMatchNoneRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.optionMatchSomeRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.eitherMatchInlRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.eitherMatchInrRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.idJReflRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.idStrictRecReflRowFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.orientedRootFiringToOrientedHeadStep

#assert_no_axioms FX1Poly.Core.orientedTableStepToIotaStep

end FX1PolyAudit
