import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatWhiskerEngines

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatWhiskerEnginesAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the four per-letter whisker engines and the fueled per-letter peels.
Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.emptyGapSlot
#print axioms FX1Poly.Polygraph.Amalgam.interleaveRuns_frontRun
#print axioms FX1Poly.Polygraph.Amalgam.readingConsSlot
#print axioms FX1Poly.Polygraph.Amalgam.whiskerLeftSEngine
#print axioms FX1Poly.Polygraph.Amalgam.tFuseHeadSlot
#print axioms FX1Poly.Polygraph.Amalgam.whiskerLeftTCore
#print axioms FX1Poly.Polygraph.Amalgam.whiskerLeftTEngine
#print axioms FX1Poly.Polygraph.Amalgam.tFuseTailSlot
#print axioms FX1Poly.Polygraph.Amalgam.whiskerRightTCore
#print axioms FX1Poly.Polygraph.Amalgam.whiskerRightTEngine
#print axioms FX1Poly.Polygraph.Amalgam.whiskerRightSCore
#print axioms FX1Poly.Polygraph.Amalgam.whiskerRightSEngine
#print axioms FX1Poly.Polygraph.Amalgam.readingWhiskerLeftFueled
#print axioms FX1Poly.Polygraph.Amalgam.readingWhiskerRightFueled
#print axioms FX1Poly.Polygraph.Amalgam.readingWhiskerLeft
#print axioms FX1Poly.Polygraph.Amalgam.readingWhiskerRight
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFlatWhiskerEngines

end FX1PolyAudit
