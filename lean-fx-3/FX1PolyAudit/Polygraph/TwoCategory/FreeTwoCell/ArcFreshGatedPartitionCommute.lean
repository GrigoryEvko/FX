import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshGatedPartitionCommute

/-! # FX1PolyAudit … ArcFreshGatedPartitionCommute — zero-axiom gate (mode-3 floor, forest-gated residual)

Per-declaration zero-axiom gate for the freshness+forest-conditioned Godement arc residual and its reduction from
the LIVE count route: the residual `ArcGodementSamePartitionFreshForest`, the reduction
`arcGodementSamePartitionFreshForest_of_coreSwapSimCount` (assembled from
`arcGodementSwapRenameable_pointwise_of_coreSwapSimCount` + `sameArcPartition_of_renameRel`), and the honesty
markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project
`#assert_no_axioms` macro is fuel-based, so each declaration is ALSO checked by the exhaustive core `#print axioms`.
NOT registered in `AuditAll` here (the orchestrator does the unified registration in one breath). -/

namespace FX1PolyAudit

-- the freshness+forest-gated residual
#assert_no_axioms FX1Poly.Polygraph.ArcGodementSamePartitionFreshForest
#print axioms FX1Poly.Polygraph.ArcGodementSamePartitionFreshForest

-- the reduction from the LIVE count route
#assert_no_axioms FX1Poly.Polygraph.arcGodementSamePartitionFreshForest_of_coreSwapSimCount
#print axioms FX1Poly.Polygraph.arcGodementSamePartitionFreshForest_of_coreSwapSimCount

-- the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcForestFreshResidualBundled
#print axioms FX1Poly.Polygraph.fxMode_hasArcForestFreshResidualBundled
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcForestFreshResidualClosed
#print axioms FX1Poly.Polygraph.fxMode_hasArcForestFreshResidualClosed

end FX1PolyAudit
