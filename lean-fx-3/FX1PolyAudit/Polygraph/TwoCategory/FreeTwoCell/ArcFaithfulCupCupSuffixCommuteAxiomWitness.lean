import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulCupCupSuffixCommute

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcFaithfulCupCupSuffixCommuteAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the faithful-engine
cup-cup suffix extract commutation: the partition-level crossing step, the faithful per-atom dispatcher, the
admissibility predicate, THE SUFFIX FOLD, the event-length accounting, the assembly, THE DELIVERY, the
non-vacuity + refl-failure probe, and the marker + pins.  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.arcPartitionSim_stepCrossArc
#print axioms FX1Poly.Polygraph.arcPartitionSim_stepArcAtomFaithful
#print axioms FX1Poly.Polygraph.SpineAdmissibleFaithful
#print axioms FX1Poly.Polygraph.arcPartitionSim_processArcSpineFaithful
#print axioms FX1Poly.Polygraph.stepArcAtomFaithful_cupEventNodes_length
#print axioms FX1Poly.Polygraph.stepArcAtomFaithful_capEventNodes_length
#print axioms FX1Poly.Polygraph.processArcSpineFaithful_cupEventNodes_length
#print axioms FX1Poly.Polygraph.processArcSpineFaithful_capEventNodes_length
#print axioms FX1Poly.Polygraph.extractArc_eq_rest_faithful_of_swapCorePackage
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixExtractCommute
#print axioms FX1Poly.Polygraph.cupCupSuffixProbeSeed
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_nonvacuous
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_statesDiffer
#print axioms FX1Poly.Polygraph.fxMode_hasArcFaithfulCupCupSuffixCommute
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_generalSignature_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcFaithfulCupCupSuffixCommute_swapRenameableProof2_stays_false

end FX1PolyAudit
