import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision — zero-axiom gate (mode-3 floor, freshness plumbing)

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
#assert_no_axioms FX1Poly.Polygraph.mem_append_imp
#assert_no_axioms FX1Poly.Polygraph.mem_natListInsertAt_imp
#assert_no_axioms FX1Poly.Polygraph.mem_natListRemoveTwoAt_imp
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_mem_or_zero
#assert_no_axioms FX1Poly.Polygraph.mem_map_imp
#assert_no_axioms FX1Poly.Polygraph.mem_iterRemoveTwoAt
#assert_no_axioms FX1Poly.Polygraph.unionFindParent_mem
#assert_no_axioms FX1Poly.Polygraph.unionFindRoot_lt
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_lt
#assert_no_axioms FX1Poly.Polygraph.unionFindJoin_edges_lt
#assert_no_axioms FX1Poly.Polygraph.lt_add_right_of_lt

-- per-branch freshness preservation
#assert_no_axioms FX1Poly.Polygraph.arcStateFresh_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.arcStateFresh_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.arcBoxStep
#assert_no_axioms FX1Poly.Polygraph.arcStateFresh_arcBoxStep

-- the dispatch + monotonicity + whole-spine fold
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_nextFresh_le
#assert_no_axioms FX1Poly.Polygraph.arcStateFresh_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcStateFresh_processArcSpine

-- the freshness-gated godement invariant reduced to the hypothesis ArcGodementSamePartitionFresh
#assert_no_axioms FX1Poly.Polygraph.godementInvariantFresh_of_samePartitionFresh

-- the freshness-threaded trace invariance + assembled soundness + decision corollary
#assert_no_axioms FX1Poly.Polygraph.arcTraceInvariantFresh
#assert_no_axioms FX1Poly.Polygraph.arcStructureOf_sound_of_arcGodementSamePartitionFresh
#assert_no_axioms FX1Poly.Polygraph.decidableTwoCellConvFull_of_fresh

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFreshSoundnessReduction

end FX1PolyAudit
