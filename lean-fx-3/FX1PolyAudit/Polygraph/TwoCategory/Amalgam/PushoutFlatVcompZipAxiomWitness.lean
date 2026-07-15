import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatVcompZip

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatVcompZipAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the vcomp payload zip, the vcomp arm, and the total flat reader over all five constructors.
Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.castBoundary_hcomp_distribute
#print axioms FX1Poly.Polygraph.Amalgam.vcomp_castBoundary_merge
#print axioms FX1Poly.Polygraph.Amalgam.consAlign_head
#print axioms FX1Poly.Polygraph.Amalgam.consAlign_tail
#print axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.ofCellEq
#print axioms FX1Poly.Polygraph.Amalgam.RunReading.cellEqTransport
#print axioms FX1Poly.Polygraph.Amalgam.zipHeadSlot
#print axioms FX1Poly.Polygraph.Amalgam.zipTailSlots
#print axioms FX1Poly.Polygraph.Amalgam.zipTailSlots_gapDom
#print axioms FX1Poly.Polygraph.Amalgam.zipTailSlots_gapCod
#print axioms FX1Poly.Polygraph.Amalgam.flatAlignEq
#print axioms FX1Poly.Polygraph.Amalgam.zipReading
#print axioms FX1Poly.Polygraph.Amalgam.vcompReading
#print axioms FX1Poly.Polygraph.Amalgam.readCellFueled
#print axioms FX1Poly.Polygraph.Amalgam.readCellIntoSlots
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasVcompPayloadZip

end FX1PolyAudit
