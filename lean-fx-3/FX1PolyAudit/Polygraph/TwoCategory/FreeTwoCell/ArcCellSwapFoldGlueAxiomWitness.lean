import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellSwapFoldGlue

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCellSwapFoldGlueAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r27
whole-cell fold glue.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.mapComposition
#print axioms FX1Poly.Polygraph.arcStepSimCount_refl
#print axioms FX1Poly.Polygraph.arcStepSimCount_comp
#print axioms FX1Poly.Polygraph.runArcCell_vcomp
#print axioms FX1Poly.Polygraph.runArcCell_whiskerLeft
#print axioms FX1Poly.Polygraph.runArcCell_whiskerRight
#print axioms FX1Poly.Polygraph.runArcCell_gen
#print axioms FX1Poly.Polygraph.fxMode_hasArcCellSwapFoldGlue
#print axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_samePartitionFresh_stays_false

end FX1PolyAudit
