import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWholeCellDisjointSupportCommute

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcWholeCellDisjointSupportCommuteAxiomWitness — independent #print axioms (MODE-COMMUTE r28)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r28
Godement-inner-shape packaging + adjudication brick.  Each must print "does not depend on any
axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.arcGodementInnerSwapSimCount
#print axioms FX1Poly.Polygraph.arcGodementInnerSwap_firedOnCounitInstance
#print axioms FX1Poly.Polygraph.unitCupCell
#print axioms FX1Poly.Polygraph.arcWhiskerSupportListEquality_refutedOnGenCells
#print axioms FX1Poly.Polygraph.arcWhiskerSupportGenCells_linksLiterallyEqual
#print axioms FX1Poly.Polygraph.fxMode_hasWholeCellDisjointSupportCommute
#print axioms FX1Poly.Polygraph.arcWholeCellCommute_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcWholeCellCommute_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcWholeCellCommute_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcWholeCellCommute_samePartitionFresh_stays_false
#print axioms FX1Poly.Polygraph.arcWholeCellCommute_blockCommute_stays_false

end FX1PolyAudit
