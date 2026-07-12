import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapWires

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapWiresAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the pure two-cup Godement
block swap: the position-freedom of a cup's links, the two-cup links byte-identity and companions, the open-wire
block transform, the concrete non-vacuity witnesses, and the honesty markers / false-keystone pins.  Each must
print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stepCupArc_links_positionFree
#print axioms FX1Poly.Polygraph.stepCupArc_nextFresh_positionFree
#print axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_links_eq
#print axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_nextFresh_eq
#print axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_loops_eq
#print axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_cupEventNodes_eq
#print axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_capEventNodes_eq
#print axioms FX1Poly.Polygraph.stepCupArc_stepCupArc_openWires_blockSwap
#print axioms FX1Poly.Polygraph.twoCupSwap_concrete_links
#print axioms FX1Poly.Polygraph.twoCupSwap_concrete_openWires
#print axioms FX1Poly.Polygraph.fxMode_hasArcTwoCupSwapLinksBytewiseIdentical
#print axioms FX1Poly.Polygraph.fxMode_hasArcTwoCupSwapOpenWireBlockTransform
#print axioms FX1Poly.Polygraph.fxMode_hasArcTwoCupGodementSwapSim
#print axioms FX1Poly.Polygraph.arcGodementSamePartitionFreshProof_staysFalse
#print axioms FX1Poly.Polygraph.arcPeelGeneralSignature_staysFalse
#print axioms FX1Poly.Polygraph.arcGodementSwapRenameableProof2_staysFalse

end FX1PolyAudit
