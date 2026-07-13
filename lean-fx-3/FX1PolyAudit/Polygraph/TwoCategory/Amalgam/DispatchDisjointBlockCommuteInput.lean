import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchDisjointBlockCommuteInput

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.DispatchDisjointBlockCommuteInput — zero-axiom gate (WP-AMALG, r28 input)

Per-declaration zero-axiom gate for the dispatch's supplied `componentComm` input: the
pushout-signature block-commutation theorem, the thin-pushout-typed fire, the content-fire
fixtures with their kernel-pinned order-invariant data, the shipped marker, and the three
untouched-false dispatch pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutDisjointBlockCommuteInput
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinPushoutOnlyMode
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinPushoutFireSeed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.thinPushoutFireSeed_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutDisjointBlockCommuteInput_firedAtThinPushout
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchContentFireRedex
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchContentFireReduct
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchContentFire_orderInvariantData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasDispatchDisjointBlockCommuteInput
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchDisjointBlockCommuteInput_saturatedDispatch_stays_false
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchDisjointBlockCommuteInput_closeCriterion_stays_false
#assert_no_axioms FX1Poly.Polygraph.Amalgam.dispatchDisjointBlockCommuteInput_blockCommute_stays_false

end FX1PolyAudit
