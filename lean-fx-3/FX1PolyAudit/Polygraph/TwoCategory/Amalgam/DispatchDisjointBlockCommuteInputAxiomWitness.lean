import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchDisjointBlockCommuteInput

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DispatchDisjointBlockCommuteInputAxiomWitness — independent #print axioms (WP-AMALG, r28 input)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the supplied
dispatch `componentComm` input.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.pushoutDisjointBlockCommuteInput
#print axioms FX1Poly.Polygraph.Amalgam.thinPushoutOnlyMode
#print axioms FX1Poly.Polygraph.Amalgam.thinPushoutFireSeed
#print axioms FX1Poly.Polygraph.Amalgam.thinPushoutFireSeed_isWellFormed
#print axioms FX1Poly.Polygraph.Amalgam.pushoutDisjointBlockCommuteInput_firedAtThinPushout
#print axioms FX1Poly.Polygraph.Amalgam.dispatchContentFireRedex
#print axioms FX1Poly.Polygraph.Amalgam.dispatchContentFireReduct
#print axioms FX1Poly.Polygraph.Amalgam.dispatchContentFire_orderInvariantData
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasDispatchDisjointBlockCommuteInput
#print axioms FX1Poly.Polygraph.Amalgam.dispatchDisjointBlockCommuteInput_saturatedDispatch_stays_false
#print axioms FX1Poly.Polygraph.Amalgam.dispatchDisjointBlockCommuteInput_closeCriterion_stays_false
#print axioms FX1Poly.Polygraph.Amalgam.dispatchDisjointBlockCommuteInput_blockCommute_stays_false

end FX1PolyAudit
