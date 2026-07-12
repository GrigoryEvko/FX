import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGodementFreshForestGapRefutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGodementFreshForestGapRefutationAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every shipped declaration of the FOREST-GAP adjudication (r21,
branch (a)): the fresh-but-cyclic counterexample witnesses, the decided CAP-event divergence, the refutation of the
literal fresh residual, the honesty marker, and the two graveyard pins.  Each must print "does not depend on any
axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.arcFreshCyclicForestGapState_isFresh
#print axioms FX1Poly.Polygraph.arcFreshCyclicForestGapLinks_notForest
#print axioms FX1Poly.Polygraph.arcFreshCyclicForestGapState_notForest
#print axioms FX1Poly.Polygraph.bottomCountBelowFresh
#print axioms FX1Poly.Polygraph.internalCapCountAtPortZero_differs
#print axioms FX1Poly.Polygraph.not_arcGodementSamePartitionFresh
#print axioms FX1Poly.Polygraph.fxMode_hasArcGodementSamePartitionFreshRefuted
#print axioms FX1Poly.Polygraph.arcGodementFreshForestGapRefutation_samePartitionFreshProof_stays_false
#print axioms FX1Poly.Polygraph.arcGodementFreshForestGapRefutation_forestResidualClosed_stays_false

end FX1PolyAudit
