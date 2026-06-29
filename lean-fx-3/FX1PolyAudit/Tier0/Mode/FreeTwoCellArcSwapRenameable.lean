import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellArcSwapRenameable

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellArcSwapRenameable — zero-axiom gate (mode-3 floor, leg B, W2-ArcSwap)

Per-declaration zero-axiom gate for the Godement block-swap renaming foundation: the propext-free list-map
helpers (`mapAppend` / `natListInsertAt_map` / `natListRemoveTwoAt_map` / `natListGetAt_map` / `mapFixedAbove` /
`mem_mapAdd_ge` / `mapLength` / `mapFixedOn`), the union-find join renaming-commutation
(`renameLinks_unionFindJoin`), the per-root event-count renaming / additivity (`countEventsInRoot_rename` /
`countEventsInRoot_append`), `nextFresh` monotonicity (`stepArcAtom_nextFresh_le` /
`processArcSpine_nextFresh_le` / `runArcCell_nextFresh_le`), the arc-fold renaming-equivariance (`renameState` /
`stepCupArc_renameState` / `stepCapArc_renameState` / `droppedWires_map` / `stepArcAtom_renameState` /
`processArcSpine_renameState` / `runArcCell_renameState`), the `ArcRenameRel` bridge and extract
renaming-invariance (`boundaryNodesOf_renameState` / `renameRel_of_renameState` / `extractArc_renameState`), and
the honesty markers.

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

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasUnionFindJoinRenameCommute
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcFoldRenamingEquivariance
#assert_no_axioms FX1Poly.Tier0.fxMode_hasExtractArcRenamingInvariance
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementSwapRenameableProof2

end FX1PolyAudit
