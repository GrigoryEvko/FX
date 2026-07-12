import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderCapCapClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderCapCapClosureAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every declaration of the CAP x CAP faithful reorder sibling
closure (r20): the port, the sibling relation, the cap-cap smart constructor, the embedding, THE EXTENDED
CLOSURE THEOREM, the four-partition-family fires + refl-failure probes + the MIXED witness, and the marker +
pins.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.arcFaithfulCapCapSuffixExtractCommute
#print axioms FX1Poly.Polygraph.FaithfulReorderEquivWithCapCap
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCapCap
#print axioms FX1Poly.Polygraph.reorderWithCapCap_of_faithfulReorder
#print axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulReorderEquivWithCapCap
#print axioms FX1Poly.Polygraph.capCapReorder_witness
#print axioms FX1Poly.Polygraph.capCapReorder_extractEq
#print axioms FX1Poly.Polygraph.capCapReorder_statesDiffer
#print axioms FX1Poly.Polygraph.cupCupReorder_extractEq
#print axioms FX1Poly.Polygraph.cupCupReorder_statesDiffer
#print axioms FX1Poly.Polygraph.cupCapSuffixExtractCommute
#print axioms FX1Poly.Polygraph.cupCapSuffix_statesDiffer
#print axioms FX1Poly.Polygraph.capCupSuffixExtractCommute
#print axioms FX1Poly.Polygraph.capCupSuffix_statesDiffer
#print axioms FX1Poly.Polygraph.mixedCapCapReorderWitness
#print axioms FX1Poly.Polygraph.mixedCapCapReorder_extractEq
#print axioms FX1Poly.Polygraph.mixedCapCapReorder_statesDiffer
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulReorderCapCapExtractInvariance
#print axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderCapCapClosure_swapRenameableProof2_stays_false

end FX1PolyAudit
