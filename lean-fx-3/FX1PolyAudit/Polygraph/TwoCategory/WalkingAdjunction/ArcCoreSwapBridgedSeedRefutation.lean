import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCoreSwapBridgedSeedRefutation

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.ArcCoreSwapBridgedSeedRefutation — zero-axiom gate (MODE-COMMUTE r29)

Per-declaration zero-axiom gate for the `ArcGodementCoreSwapSimCount` bridged-seed decision:
the pre-bridged seed fixtures, the two run orders with their whole-record kernel pins, the
old-root-asymmetry pin, THE REFUTATION, the sharpness companion (small-boundary satisfiability
via the root transposition), and the adjudication pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.bridgedSwapSeedState
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapNilBase
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapMidPath
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapCommonPrefixCell
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapSeedState_isFresh
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapSeedState_isForest
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapSeedState_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapSeedState_violatesWindowGuard
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRedexRun
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapReductRun
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRedexValue
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapReductValue
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRedexRun_valueEq
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapReductRun_valueEq
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRuns_oldRootAsymmetry
#assert_no_axioms FX1Poly.Polygraph.not_arcGodementCoreSwapSimCount_atBridgedSeed
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRootTransposition
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRootTransposition_involution
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRootTransposition_injective
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapRedexValue_isForest
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapReductValue_isForest
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapValues_simCount
#assert_no_axioms FX1Poly.Polygraph.bridgedSwapInstance_smallBoundarySatisfiable
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCoreSwapBridgedSeedDecision
#assert_no_axioms FX1Poly.Polygraph.arcCoreSwapRefutation_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCoreSwapRefutation_swapRenameableProof_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCoreSwapRefutation_capFlipRefutationStands

end FX1PolyAudit
