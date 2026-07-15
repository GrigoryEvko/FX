import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatReading

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatReadingAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the run reading structure with its transports, the id/gen arms, the flat identity collapse, and the head-absorption engines.
Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.RunReading
#print axioms FX1Poly.Polygraph.Amalgam.RunReading.mapConv
#print axioms FX1Poly.Polygraph.Amalgam.RunReading.castTransport
#print axioms FX1Poly.Polygraph.Amalgam.allRunsWallFree_head
#print axioms FX1Poly.Polygraph.Amalgam.allRunsWallFree_tail
#print axioms FX1Poly.Polygraph.Amalgam.idSlotsOfRuns
#print axioms FX1Poly.Polygraph.Amalgam.idSlotsOfRuns_gapDom
#print axioms FX1Poly.Polygraph.Amalgam.idSlotsOfRuns_gapCod
#print axioms FX1Poly.Polygraph.Amalgam.idHeadSlot
#print axioms FX1Poly.Polygraph.Amalgam.idSlots_flatDom_eq_flatCod
#print axioms FX1Poly.Polygraph.Amalgam.flatIdCollapse
#print axioms FX1Poly.Polygraph.Amalgam.idSlots_flatDom
#print axioms FX1Poly.Polygraph.Amalgam.idSlots_flatCod
#print axioms FX1Poly.Polygraph.Amalgam.idConvOfCollapse
#print axioms FX1Poly.Polygraph.Amalgam.idReading
#print axioms FX1Poly.Polygraph.Amalgam.genSourceWallFree
#print axioms FX1Poly.Polygraph.Amalgam.genTargetWallFree
#print axioms FX1Poly.Polygraph.Amalgam.genReading
#print axioms FX1Poly.Polygraph.Amalgam.hcompIdNilLeftConv
#print axioms FX1Poly.Polygraph.Amalgam.whiskerLeftHcompFuse
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFlatReadingBaseArms

end FX1PolyAudit
