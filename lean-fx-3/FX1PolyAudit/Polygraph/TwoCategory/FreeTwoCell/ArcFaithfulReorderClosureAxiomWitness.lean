import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulReorderClosureAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every declaration of the FAITHFUL reorder closure: the
equivalence relation, the six smart constructors, THE CLOSURE THEOREM, the two per-arm single-step corollaries,
the non-vacuity MIXED witness / closure firing / refl-failure probe / genuine literal node, and the marker +
pins.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.FaithfulReorderEquiv
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCross
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCupCross
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCup
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCapCross
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCrossCap
#print axioms FX1Poly.Polygraph.faithfulReorder_ofCupCup
#print axioms FX1Poly.Polygraph.extractArc_eq_of_faithfulReorderEquiv
#print axioms FX1Poly.Polygraph.extractArc_eq_ofCrossCrossReorderStep
#print axioms FX1Poly.Polygraph.extractArc_eq_ofCupCupReorderStep
#print axioms FX1Poly.Polygraph.literalCrossReorder_witness
#print axioms FX1Poly.Polygraph.mixedReorderWitness
#print axioms FX1Poly.Polygraph.mixedReorder_extractEq
#print axioms FX1Poly.Polygraph.mixedReorder_statesDiffer
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulReorderExtractInvariance
#print axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulReorderClosure_swapRenameableProof2_stays_false

end FX1PolyAudit
