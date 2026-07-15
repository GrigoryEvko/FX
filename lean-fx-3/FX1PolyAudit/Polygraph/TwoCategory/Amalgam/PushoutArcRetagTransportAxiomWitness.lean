import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutArcRetagTransport

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutArcRetagTransportAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the arc
retag transport brick.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.stepArcAtom_crossSignatureCongr
#print axioms FX1Poly.Polygraph.Amalgam.processArcSpine_mapCellAlong
#print axioms FX1Poly.Polygraph.Amalgam.runArcCell_mapCellAlong
#print axioms FX1Poly.Polygraph.Amalgam.isTurnbackOnly_castBoundary
#print axioms FX1Poly.Polygraph.Amalgam.isTurnbackOnly_mapCellAlong
#print axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadBaseMode
#print axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadNilBase
#print axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadUnitCupCell
#print axioms FX1Poly.Polygraph.Amalgam.arcRetagFireSeed
#print axioms FX1Poly.Polygraph.Amalgam.arcRetagTransport_firedOnDoubleAdjunction
#print axioms FX1Poly.Polygraph.Amalgam.arcRetagTransport_fireData
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasPushoutArcRetagTransport

end FX1PolyAudit
