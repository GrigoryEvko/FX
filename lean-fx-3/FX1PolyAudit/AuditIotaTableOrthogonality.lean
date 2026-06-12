import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableOrthogonality

/-! # FX1PolyAudit/AuditIotaTableOrthogonality — IOTA-T5 audit shard

Per-declaration zero-axiom gate for the orthogonality certificate: the
decidable well-formedness checkers, the canonical 18-row table's
`rfl`-decided certificate (the permanent guard that re-decides on every
new row), the pairwise extraction lemmas, the head-pinning bricks, and
the ★ root-firing determinism keystone that collapses the quadratic
`cd_lemma` SameRoot/SourcesDisjoint arm matrix.  Every declaration
below must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The Bool fold + row keys -/

#assert_no_axioms FX1Poly.Core.listForall
#assert_no_axioms FX1Poly.Core.listForall_mem
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.primarySlot?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.primaryHead?
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.rootKey

/-! ## The decidable checkers + the bundled predicate -/

#assert_no_axioms FX1Poly.Core.rowKeysDiffer
#assert_no_axioms FX1Poly.Core.allRootKeysDistinct
#assert_no_axioms FX1Poly.Core.elimDeterminesSlot
#assert_no_axioms FX1Poly.Core.allElimDetermineSlot
#assert_no_axioms FX1Poly.Core.elimRootsAvoidScrutineeHeads
#assert_no_axioms FX1Poly.Core.tableElimRoots
#assert_no_axioms FX1Poly.Core.allElimRootsAvoidScrutineeHeads
#assert_no_axioms FX1Poly.Core.allRowsHavePrimaryScrutinee
#assert_no_axioms FX1Poly.Core.WfIotaTable

/-! ## The canonical-table certificate (the permanent audit guard) -/

#assert_no_axioms FX1Poly.Core.iotaRuleTable_isWf

/-! ## Head pinning + non-emptiness extraction -/

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.scrutineeSpecFires_slotHoldsHead
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_pinsPrimaryHead
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_pinsElim
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.consScrutineesOfPrimarySome

/-! ## Pairwise extraction -/

#assert_no_axioms FX1Poly.Core.allRootKeysDistinct_memUnique
#assert_no_axioms FX1Poly.Core.allElimDetermineSlot_pairwise

/-! ## The keystone: root determinism -/

#assert_no_axioms FX1Poly.Core.WfIotaTable.rootFiringDeterministic
#assert_no_axioms FX1Poly.Core.WfIotaTable.fireTableRedexOver_eq_ofRowFires
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_atOwnElim

end FX1PolyAudit
