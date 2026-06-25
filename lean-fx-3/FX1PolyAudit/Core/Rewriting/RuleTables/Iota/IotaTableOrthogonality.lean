import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrthogonality

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableOrthogonality

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrthogonality`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ THE TABLE-ROUTED RAW CONFLUENCE (StepStarConfluenceViaTable.lean) — the bespoke-iota
-- retirement's decoupling brick.  The canonical 21-row table carries its well-formedness
-- (iotaRuleTable_isWf, rfl-decidable enumeration checks) and scope-uniformity
-- (iotaRuleTable_isScopeUniform) certificates, so the generic orthogonal-systems table confluence
-- instantiates at
-- it (StepOverTable.canonicalConfluent).  The IOTA-T1 adequacy lifts to stars in both directions
-- (StepStar.toTableClosure / ReflTransClosure.toStepStar), and the headlines
-- transport: StepStar.tableRouteConfluence (many-vs-many) + StepStar.tableRouteStrip
-- (one-vs-many) — NO parallel-reduction sandwich, NO complete development, NO per-iota
-- critical-pair matrix.
#assert_no_axioms FX1Poly.Core.iotaRuleTable_isWf

#assert_no_axioms FX1Poly.Core.listForall

#assert_no_axioms FX1Poly.Core.listForall_mem

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.primarySlot?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.primaryHead?

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.rootKey

#assert_no_axioms FX1Poly.Core.rowKeysDiffer

#assert_no_axioms FX1Poly.Core.allRootKeysDistinct

#assert_no_axioms FX1Poly.Core.elimDeterminesSlot

#assert_no_axioms FX1Poly.Core.allElimDetermineSlot

#assert_no_axioms FX1Poly.Core.elimRootsAvoidScrutineeHeads

#assert_no_axioms FX1Poly.Core.tableElimRoots

#assert_no_axioms FX1Poly.Core.allElimRootsAvoidScrutineeHeads

#assert_no_axioms FX1Poly.Core.allRowsHavePrimaryScrutinee

#assert_no_axioms FX1Poly.Core.WfIotaTable

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_slotHoldsHead

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_pinsPrimaryHead

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_pinsElim

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.consScrutineesOfPrimarySome

#assert_no_axioms FX1Poly.Core.allRootKeysDistinct_memUnique

#assert_no_axioms FX1Poly.Core.allElimDetermineSlot_pairwise

#assert_no_axioms FX1Poly.Core.WfIotaTable.rootFiringDeterministic

#assert_no_axioms FX1Poly.Core.WfIotaTable.fireTableRedexOver_eq_ofRowFires

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_atOwnElim

end FX1PolyAudit
