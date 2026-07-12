import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCompoundBlockTransposition

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCompoundBlockTranspositionAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the COMPOUND
fresh-block transposition (MODE-COMMUTE r22): the carrier reconciliation, the compound sigma, the
four UF-automorphism obligations, the two renaming-commutation cruxes, the consumer-shaped
below-base fixing bridge, the two firing probes, the marker, and the r23-open honesty pin.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.blockRotate_eq_arcFreshBlockTransposition
#print axioms FX1Poly.Polygraph.compoundFreshBlockTransposition
#print axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_fixesZero
#print axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_fixesBelow
#print axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_fixesAbove
#print axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_leftInverse
#print axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_injective
#print axioms FX1Poly.Polygraph.unionFindRootOf_compoundTransposition
#print axioms FX1Poly.Polygraph.isSameComponent_compoundTransposition
#print axioms FX1Poly.Polygraph.renameLinks_compoundTransposition_ofBelow
#print axioms FX1Poly.Polygraph.compoundFreshBlockTransposition_shapes_probe
#print axioms FX1Poly.Polygraph.isSameComponent_compoundTransposition_probe
#print axioms FX1Poly.Polygraph.fxMode_hasCompoundFreshBlockTransposition
#print axioms FX1Poly.Polygraph.arcCompoundBlockTransposition_blockSwapCore_stays_open

end FX1PolyAudit
