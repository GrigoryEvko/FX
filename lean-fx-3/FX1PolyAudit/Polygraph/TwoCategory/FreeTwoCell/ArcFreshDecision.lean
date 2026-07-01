import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellArcFreshDecision — zero-axiom gate (mode-3 floor, freshness plumbing)

Per-declaration zero-axiom gate for the FRESHNESS-gated arc-soundness plumbing that closes the consumer's
`godementInvariant` from the actual reachable (always-fresh) states: the `propext`-free list / union-find
membership-and-bound helpers (`mem_append_imp` … `unionFindJoin_edges_lt`, `lt_add_right_of_lt`), the per-branch
freshness preservation (`arcStateFresh_stepCupArc` / `arcStateFresh_stepCapArc` / `arcBoxStep` /
`arcStateFresh_arcBoxStep`), the dispatch + monotonicity (`stepArcAtom_nextFresh_le` /
`arcStateFresh_stepArcAtom` / `arcStateFresh_processArcSpine`), the freshness-gated `godementInvariant` reduced to
the hypothesis `ArcGodementSamePartitionFresh` (`godementInvariantFresh_of_samePartitionFresh`), the
freshness-threaded trace invariance + assembled soundness (`arcTraceInvariantFresh` /
`arcStructureOf_sound_of_arcGodementSamePartitionFresh`), the freshness-gated decision corollary
(`decidableTwoCellConvFull_of_fresh`), and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the orchestrator does the unified registration). -/

namespace FX1PolyAudit

-- the propext-free list / union-find membership and bound helpers
#assert_no_axioms FX1Poly.Tier0.mem_append_imp
#assert_no_axioms FX1Poly.Tier0.mem_natListInsertAt_imp
#assert_no_axioms FX1Poly.Tier0.mem_natListRemoveTwoAt_imp
#assert_no_axioms FX1Poly.Tier0.natListGetAt_mem_or_zero
#assert_no_axioms FX1Poly.Tier0.mem_map_imp
#assert_no_axioms FX1Poly.Tier0.mem_iterRemoveTwoAt
#assert_no_axioms FX1Poly.Tier0.unionFindParent_mem
#assert_no_axioms FX1Poly.Tier0.unionFindRoot_lt
#assert_no_axioms FX1Poly.Tier0.unionFindRootOf_lt
#assert_no_axioms FX1Poly.Tier0.unionFindJoin_edges_lt
#assert_no_axioms FX1Poly.Tier0.lt_add_right_of_lt

-- per-branch freshness preservation
#assert_no_axioms FX1Poly.Tier0.arcStateFresh_stepCupArc
#assert_no_axioms FX1Poly.Tier0.arcStateFresh_stepCapArc
#assert_no_axioms FX1Poly.Tier0.arcBoxStep
#assert_no_axioms FX1Poly.Tier0.arcStateFresh_arcBoxStep

-- the dispatch + monotonicity + whole-spine fold
#assert_no_axioms FX1Poly.Tier0.stepArcAtom_nextFresh_le
#assert_no_axioms FX1Poly.Tier0.arcStateFresh_stepArcAtom
#assert_no_axioms FX1Poly.Tier0.arcStateFresh_processArcSpine

-- the freshness-gated godement invariant reduced to the hypothesis ArcGodementSamePartitionFresh
#assert_no_axioms FX1Poly.Tier0.godementInvariantFresh_of_samePartitionFresh

-- the freshness-threaded trace invariance + assembled soundness + decision corollary
#assert_no_axioms FX1Poly.Tier0.arcTraceInvariantFresh
#assert_no_axioms FX1Poly.Tier0.arcStructureOf_sound_of_arcGodementSamePartitionFresh
#assert_no_axioms FX1Poly.Tier0.decidableTwoCellConvFull_of_fresh

-- honesty marker
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcFreshSoundnessReduction

end FX1PolyAudit
