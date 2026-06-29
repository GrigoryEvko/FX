import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellArcSwapRenameable

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellArcSwapRenameable — zero-axiom gate (mode-3 floor, leg B, W2-ArcSwap)

Per-declaration zero-axiom gate for the Godement block-swap renaming foundation: the propext-free list-map
helpers (`mapAppend` / `natListInsertAt_map` / `natListRemoveTwoAt_map` / `natListGetAt_map` / `mapFixedAbove` /
`mem_mapAdd_ge` / `mapLength` / `mapFixedOn`), the union-find join renaming-commutation
(`renameLinks_unionFindJoin`), the forest / acyclicity invariant that discharges the `settles` precondition
unconditionally and is preserved through the whole fold (`isUnionFindForest` / `unionFindRootOf_parentless_of_forest`
/ `unionFindRootOf_consJoin` / the `isUnionFindForest_*` preservation chain), the per-root event-count renaming /
additivity (`countEventsInRoot_rename` / `countEventsInRoot_append`), `nextFresh` monotonicity
(`stepArcAtom_nextFresh_le` /
`processArcSpine_nextFresh_le` / `runArcCell_nextFresh_le`), the arc-fold renaming-equivariance (`renameState` /
`stepCupArc_renameState` / `stepCapArc_renameState` / `droppedWires_map` / `stepArcAtom_renameState` /
`processArcSpine_renameState` / `runArcCell_renameState`), the `ArcRenameRel` bridge and extract
renaming-invariance (`boundaryNodesOf_renameState` / `renameRel_of_renameState` / `extractArc_renameState`), the
suffix-peel reducing the full block-swap to the core swap (`processArcSpine_runArcCell_renameState` /
`ArcGodementCoreSwapRenameable` / `arcGodementSwapRenameable_of_coreSwap`), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the orchestrator does the unified registration). -/

namespace FX1PolyAudit

-- propext-free list-map helpers
#assert_no_axioms FX1Poly.Tier0.mapAppend
#assert_no_axioms FX1Poly.Tier0.natListInsertAt_map
#assert_no_axioms FX1Poly.Tier0.natListRemoveTwoAt_map
#assert_no_axioms FX1Poly.Tier0.natListGetAt_map
#assert_no_axioms FX1Poly.Tier0.mapFixedAbove
#assert_no_axioms FX1Poly.Tier0.mem_mapAdd_ge
#assert_no_axioms FX1Poly.Tier0.mapLength
#assert_no_axioms FX1Poly.Tier0.mapFixedOn

-- the union-find join renaming-commutation (the clean half of obstruction 2)
#assert_no_axioms FX1Poly.Tier0.renameLinks_unionFindJoin

-- root-following after a disjoint-range union (the other half of obstruction 2)
#assert_no_axioms FX1Poly.Tier0.unionFindRoot_of_parentless
#assert_no_axioms FX1Poly.Tier0.unionFindRootOf_of_parentless
#assert_no_axioms FX1Poly.Tier0.unionFindParent_none_of_lt
#assert_no_axioms FX1Poly.Tier0.unionFindParent_none_of_freshNode
#assert_no_axioms FX1Poly.Tier0.unionFindRoot_consJoin

-- the forest / acyclicity invariant: settling discharged + preservation through the whole fold
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_cons
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_nil
#assert_no_axioms FX1Poly.Tier0.unionFindRootOf_parentless_of_forest
#assert_no_axioms FX1Poly.Tier0.unionFindRootOf_consJoin
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_unionFindJoin
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_stepCupArc
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_stepCapArc
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_stepArcAtom
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_processArcSpine
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_runArcCell
#assert_no_axioms FX1Poly.Tier0.isUnionFindForest_initialLinks

-- the per-root event-count renaming-covariance / additivity
#assert_no_axioms FX1Poly.Tier0.countEventsInRoot_rename
#assert_no_axioms FX1Poly.Tier0.countEventsInRoot_append

-- nextFresh monotonicity (the locality anchor)
#assert_no_axioms FX1Poly.Tier0.stepArcAtom_nextFresh_le
#assert_no_axioms FX1Poly.Tier0.processArcSpine_nextFresh_le
#assert_no_axioms FX1Poly.Tier0.runArcCell_nextFresh_le

-- the arc-fold renaming-equivariance (cup / cap / box)
#assert_no_axioms FX1Poly.Tier0.renameState
#assert_no_axioms FX1Poly.Tier0.stepCupArc_renameState
#assert_no_axioms FX1Poly.Tier0.stepCapArc_renameState
#assert_no_axioms FX1Poly.Tier0.droppedWires_map
#assert_no_axioms FX1Poly.Tier0.stepArcAtom_renameState
#assert_no_axioms FX1Poly.Tier0.processArcSpine_renameState
#assert_no_axioms FX1Poly.Tier0.runArcCell_renameState

-- the ArcRenameRel bridge + extract renaming-invariance
#assert_no_axioms FX1Poly.Tier0.boundaryNodesOf_renameState
#assert_no_axioms FX1Poly.Tier0.renameRel_of_renameState
#assert_no_axioms FX1Poly.Tier0.extractArc_renameState

-- the suffix-peel: reducing the full block-swap to the core swap
#assert_no_axioms FX1Poly.Tier0.processArcSpine_runArcCell_renameState
#assert_no_axioms FX1Poly.Tier0.ArcGodementCoreSwapRenameable
#assert_no_axioms FX1Poly.Tier0.arcGodementSwapRenameable_of_coreSwap

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasUnionFindJoinRenameCommute
#assert_no_axioms FX1Poly.Tier0.fxMode_hasUnionFindRootFollowingAfterJoin
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcFoldForestInvariant
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcFoldRenamingEquivariance
#assert_no_axioms FX1Poly.Tier0.fxMode_hasExtractArcRenamingInvariance
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcSwapSuffixPeel
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementSwapRenameableProof2

end FX1PolyAudit
