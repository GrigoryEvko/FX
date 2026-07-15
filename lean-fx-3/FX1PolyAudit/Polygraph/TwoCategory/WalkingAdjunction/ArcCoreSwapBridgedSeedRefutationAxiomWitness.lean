import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCoreSwapBridgedSeedRefutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.ArcCoreSwapBridgedSeedRefutationAxiomWitness — independent #print axioms (MODE-COMMUTE r29)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the
`ArcGodementCoreSwapSimCount` bridged-seed decision.  Each must print "does not depend on any
axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.bridgedSwapSeedState
#print axioms FX1Poly.Polygraph.bridgedSwapNilBase
#print axioms FX1Poly.Polygraph.bridgedSwapMidPath
#print axioms FX1Poly.Polygraph.bridgedSwapCommonPrefixCell
#print axioms FX1Poly.Polygraph.bridgedSwapSeedState_isFresh
#print axioms FX1Poly.Polygraph.bridgedSwapSeedState_isForest
#print axioms FX1Poly.Polygraph.bridgedSwapSeedState_isWellFormed
#print axioms FX1Poly.Polygraph.bridgedSwapSeedState_violatesWindowGuard
#print axioms FX1Poly.Polygraph.bridgedSwapRedexRun
#print axioms FX1Poly.Polygraph.bridgedSwapReductRun
#print axioms FX1Poly.Polygraph.bridgedSwapRedexValue
#print axioms FX1Poly.Polygraph.bridgedSwapReductValue
#print axioms FX1Poly.Polygraph.bridgedSwapRedexRun_valueEq
#print axioms FX1Poly.Polygraph.bridgedSwapReductRun_valueEq
#print axioms FX1Poly.Polygraph.bridgedSwapRuns_oldRootAsymmetry
#print axioms FX1Poly.Polygraph.not_arcGodementCoreSwapSimCount_atBridgedSeed
#print axioms FX1Poly.Polygraph.bridgedSwapRootTransposition
#print axioms FX1Poly.Polygraph.bridgedSwapRootTransposition_involution
#print axioms FX1Poly.Polygraph.bridgedSwapRootTransposition_injective
#print axioms FX1Poly.Polygraph.bridgedSwapRedexValue_isForest
#print axioms FX1Poly.Polygraph.bridgedSwapReductValue_isForest
#print axioms FX1Poly.Polygraph.bridgedSwapValues_simCount
#print axioms FX1Poly.Polygraph.bridgedSwapInstance_smallBoundarySatisfiable
#print axioms FX1Poly.Polygraph.fxMode_hasArcCoreSwapBridgedSeedDecision
#print axioms FX1Poly.Polygraph.arcCoreSwapRefutation_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcCoreSwapRefutation_swapRenameableProof_stays_false
#print axioms FX1Poly.Polygraph.arcCoreSwapRefutation_capFlipRefutationStands

end FX1PolyAudit
