import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementCellAscentWall

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGodementCellAscentWall — zero-axiom gate

Per-declaration zero-axiom gate for the CELL ASCENT wall characterization (r20 B2): the base-case fire
`cellAscentBase_sameArcPartition` (an atom-pair core discharges :472's conclusion shape via the shipped
readout), the FOREST GAP witness `cellAscentForestGap_freshNotForest`, the wall marker
`fxMode_hasArcGodementCellAscentWall`, and the three permanent pins.

The file flips ONLY its own NEW marker `fxMode_hasArcGodementCellAscentWall := true` (the wall is
CHARACTERIZED, not the ascent completed); the honesty pin `fxMode_hasArcGodementSamePartitionFreshProof` and
the two permanent keystones `fxMode_hasArcPeelGeneralSignature` /
`fxMode_hasArcGodementSwapRenameableProof2` stay `false` (re-asserted by `rfl`).

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the
two are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- evidence theorems
#assert_no_axioms FX1Poly.Polygraph.cellAscentBase_sameArcPartition
#assert_no_axioms FX1Poly.Polygraph.cellAscentForestGap_freshNotForest

-- wall marker + pins
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcGodementCellAscentWall
#assert_no_axioms FX1Poly.Polygraph.arcGodementCellAscentWall_samePartitionFreshProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcGodementCellAscentWall_generalSignature_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcGodementCellAscentWall_swapRenameableProof2_stays_false

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.cellAscentBase_sameArcPartition
#print axioms FX1Poly.Polygraph.cellAscentForestGap_freshNotForest
#print axioms FX1Poly.Polygraph.fxMode_hasArcGodementCellAscentWall
#print axioms FX1Poly.Polygraph.arcGodementCellAscentWall_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcGodementCellAscentWall_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcGodementCellAscentWall_swapRenameableProof2_stays_false

end FX1PolyAudit
