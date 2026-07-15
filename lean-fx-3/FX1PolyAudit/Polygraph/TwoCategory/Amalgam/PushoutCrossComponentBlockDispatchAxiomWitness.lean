import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCrossComponentBlockDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutCrossComponentBlockDispatchAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the
cross-component block dispatch brick.  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.arcWindowsListDisjointCheck
#print axioms FX1Poly.Polygraph.Amalgam.natListAllTrueOfMem
#print axioms FX1Poly.Polygraph.Amalgam.arcWindowsComponentDisjoint_ofEmptyLinksCheck
#print axioms FX1Poly.Polygraph.Amalgam.pushoutCrossComponentBlockDispatch
#print axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadLeftOnlyPath
#print axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadRightOnlyPath
#print axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadSandwichedCounitCell
#print axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadSandwichedCounitCell_isTurnbackOnly
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentFireSeed
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentFireSeed_isWellFormed
#print axioms FX1Poly.Polygraph.Amalgam.doubleAdjunctionPushoutNilBase
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_firedOnDoubleAdjunction
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentFireRedex
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentFireReduct
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentFire_orderInvariantData
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCrossComponentBlockDispatch
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_saturatedDispatch_stays_false
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_closeCriterion_stays_false
#print axioms FX1Poly.Polygraph.Amalgam.crossComponentBlockDispatch_bridgedSeedSharpnessStands

end FX1PolyAudit
