import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute — zero-axiom gate (mode-3 floor, connectivity residual)

Per-declaration zero-axiom gate for the Godement arc residual reduced to the boundary-connectivity closure: the
`propext`-free list helpers (`memRangeLoop_imp` / `mem_range_imp_lt` / `listMapCongr` / `findPartnerScan_congr`),
the boundary-connectivity view (`boundaryNodesOf` / `boundarySameComponent`), the renaming-invariance factoring
theorem (`extractArc_eq_of_partitionView`), the connectivity residual (`SameArcPartition` /
`ArcGodementSamePartition`), the reduction (`arcGodementPartitionCommute_of_sameArcPartition`), the assembled
soundness / `godementInvariant` (`arcStructureOf_sound_of_arcGodementSamePartition` /
`arcGodementInvariant_of_sameArcPartition`), the zero-axiom REFUTATION of the over-quantified residual
(`not_arcGodementSamePartition` — the unconditional `ArcGodementSamePartition` is FALSE), the corrected
freshness-conditioned residual (`ArcStateFresh` / `arcStateFresh_initial` / `ArcGodementSamePartitionFresh`), and
the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the propext-free list helpers
#assert_no_axioms FX1Poly.Tier0.memRangeLoop_imp
#assert_no_axioms FX1Poly.Tier0.mem_range_imp_lt
#assert_no_axioms FX1Poly.Tier0.listMapCongr
#assert_no_axioms FX1Poly.Tier0.findPartnerScan_congr
#assert_no_axioms FX1Poly.Tier0.diagramType_eq_of_fields

-- the boundary-connectivity view
#assert_no_axioms FX1Poly.Tier0.boundaryNodesOf
#assert_no_axioms FX1Poly.Tier0.boundarySameComponent

-- the renaming-invariance factoring theorem
#assert_no_axioms FX1Poly.Tier0.extractArc_eq_of_partitionView

-- the connectivity residual + its packaged factoring
#assert_no_axioms FX1Poly.Tier0.SameArcPartition
#assert_no_axioms FX1Poly.Tier0.extractArc_eq_of_sameArcPartition
#assert_no_axioms FX1Poly.Tier0.ArcGodementSamePartition

-- the reduction + assembly
#assert_no_axioms FX1Poly.Tier0.arcGodementPartitionCommute_of_sameArcPartition
#assert_no_axioms FX1Poly.Tier0.arcGodementInvariant_of_sameArcPartition
#assert_no_axioms FX1Poly.Tier0.arcStructureOf_sound_of_arcGodementSamePartition

-- the over-quantified residual REFUTATION (the unconditional statement is FALSE) + the corrected residual
#assert_no_axioms FX1Poly.Tier0.not_arcGodementSamePartition
#assert_no_axioms FX1Poly.Tier0.ArcStateFresh
#assert_no_axioms FX1Poly.Tier0.arcStateFresh_initial
#assert_no_axioms FX1Poly.Tier0.ArcGodementSamePartitionFresh

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcPartitionViewFactoring
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementReducedToSamePartition
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcSamePartitionProof
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcSamePartitionRefuted
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementSamePartitionFreshProof

end FX1PolyAudit
