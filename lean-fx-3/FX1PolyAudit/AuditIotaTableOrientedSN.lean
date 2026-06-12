import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableOrientedSN

/-! # FX1PolyAudit/AuditIotaTableOrientedSN — IOTA-T8 Tier-2 audit shard

Per-declaration zero-axiom gate for the substitution-freedom
classifier, the per-row tier ledger (14 oriented + 4 substituting +
the fixpoint demo), the oriented 14-row sub-table, the per-row firing
inversions into `IotaOrientedHeadStep`, the embedding into the bespoke
RPO-oriented closure, and the ★ oriented-table strong normalization.
Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The substitution-freedom classifier -/

#assert_no_axioms FX1Poly.Core.ReductTemplate.avoidsSubstitution
#assert_no_axioms FX1Poly.Core.ReductTemplateSpine.avoidsSubstitution
#assert_no_axioms FX1Poly.Core.SpineReplacements.avoidSubstitution
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.hasSubstitutionFreeReduct
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.isRpoOrientable

/-! ## The per-row tier ledger — 14 oriented rows -/

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

/-! ## The honest refusals — substituting rows + the fixpoint demo -/

#assert_no_axioms FX1Poly.Core.betaIotaRow_isNotRpoOrientable
#assert_no_axioms FX1Poly.Core.pathBetaIotaRow_isNotRpoOrientable
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_isNotRpoOrientable
#assert_no_axioms FX1Poly.Core.natRecSuccIotaRow_isNotRpoOrientable
#assert_no_axioms FX1Poly.Core.natElimSuccIotaRow_substitutes
#assert_no_axioms FX1Poly.Core.nonStructuralReassemblyDemoRule_avoidsSubstitution
#assert_no_axioms FX1Poly.Core.nonStructuralReassemblyDemoRule_isNotRpoOrientable

/-! ## The whole-table ledger pin -/

#assert_no_axioms FX1Poly.Core.iotaTableTierLedger
#assert_no_axioms FX1Poly.Core.iotaTableTierLedger_pinned

/-! ## The oriented sub-table -/

#assert_no_axioms FX1Poly.Core.orientedIotaRuleTable
#assert_no_axioms FX1Poly.Core.orientedIotaRuleTable_length
#assert_no_axioms FX1Poly.Core.orientedIotaRuleTable_eq_filter
#assert_no_axioms FX1Poly.Core.orientedRows_areRpoOrientable
#assert_no_axioms FX1Poly.Core.orientedRow_memFullTable

/-! ## Per-row firing inversions into the oriented head step -/

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

/-! ## The embedding + soundness -/

#assert_no_axioms FX1Poly.Core.orientedTableStepToIotaStep
#assert_no_axioms FX1Poly.Core.orientedTableChildrenToIotaStepChildren
#assert_no_axioms FX1Poly.Core.orientedTableStepToStep

/-! ## ★ The oriented-table strong normalization -/

#assert_no_axioms FX1Poly.Core.StepOverTable.successorOver
#assert_no_axioms FX1Poly.Core.stepOverOrientedTable_wellFounded
#assert_no_axioms FX1Poly.Core.orientedTableStep_isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.orientedTableStep_smoke

end FX1PolyAudit
