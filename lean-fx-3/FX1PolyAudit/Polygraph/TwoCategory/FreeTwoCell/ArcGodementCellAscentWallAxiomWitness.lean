import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementCellAscentWall

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGodementCellAscentWallAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every declaration of the CELL ASCENT wall characterization
(r20 B2): the base-case fire, the FOREST GAP witness, the wall marker, and the three permanent pins.  Each must
print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.cellAscentBase_sameArcPartition
#print axioms FX1Poly.Polygraph.cellAscentForestGap_freshNotForest
#print axioms FX1Poly.Polygraph.fxMode_hasArcGodementCellAscentWall
#print axioms FX1Poly.Polygraph.arcGodementCellAscentWall_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcGodementCellAscentWall_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcGodementCellAscentWall_swapRenameableProof2_stays_false

end FX1PolyAudit
