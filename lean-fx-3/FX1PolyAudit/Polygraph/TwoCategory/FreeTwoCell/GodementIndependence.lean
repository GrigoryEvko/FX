import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence — zero-axiom gate (mode-3 floor, Godement arc residual)

Per-declaration zero-axiom gate for the Godement arc-extract independence REDUCED to the two-block commutation
core: the fold-decomposition engine (`runArcCell` / `processArcSpine_spineDiff`), the sharpened residual
`ArcGodementCommute`, the reduction `arcGodementInvariant_of_commute` (the residual implies the parent's full
`godementInvariant`), the re-gated full `arcStructureOf` soundness `arcStructureOf_sound_of_arcGodementCommute`,
and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in
`AuditAll` (the parent does the unified registration). -/

namespace FX1PolyAudit

-- the fold-decomposition engine
#assert_no_axioms FX1Poly.Tier0.runArcCell
#assert_no_axioms FX1Poly.Tier0.processArcSpine_spineDiff

-- the sharpened two-block commutation residual
#assert_no_axioms FX1Poly.Tier0.ArcGodementCommute

-- the reduction + the re-gated full soundness
#assert_no_axioms FX1Poly.Tier0.arcGodementInvariant_of_commute
#assert_no_axioms FX1Poly.Tier0.arcStructureOf_sound_of_arcGodementCommute

-- the cup/cap COUNT fields discharged unconditionally (two of five fields)
#assert_no_axioms FX1Poly.Tier0.stepArcAtom_cupEventNodes_length
#assert_no_axioms FX1Poly.Tier0.stepArcAtom_capEventNodes_length
#assert_no_axioms FX1Poly.Tier0.cupAtomCount
#assert_no_axioms FX1Poly.Tier0.capAtomCount
#assert_no_axioms FX1Poly.Tier0.processArcSpine_cupEventNodes_length
#assert_no_axioms FX1Poly.Tier0.processArcSpine_capEventNodes_length
#assert_no_axioms FX1Poly.Tier0.cupAtomCount_spineDiff
#assert_no_axioms FX1Poly.Tier0.capAtomCount_spineDiff
#assert_no_axioms FX1Poly.Tier0.runArcCell_cupEventNodes_length
#assert_no_axioms FX1Poly.Tier0.runArcCell_capEventNodes_length

-- the residual sharpened to the partition fields
#assert_no_axioms FX1Poly.Tier0.fullArcStructure_eq_of_fields
#assert_no_axioms FX1Poly.Tier0.ArcGodementPartitionCommute
#assert_no_axioms FX1Poly.Tier0.arcGodementCommute_of_partitionCommute
#assert_no_axioms FX1Poly.Tier0.arcStructureOf_sound_of_arcGodementPartitionCommute

-- honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementFoldDecomposition
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementReducedToBlockCommute
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcBlockCommuteProof
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcCupCapCountFieldsDischarged
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcGodementReducedToPartitionCommute
#assert_no_axioms FX1Poly.Tier0.fxMode_hasArcPartitionCommuteProof

end FX1PolyAudit
