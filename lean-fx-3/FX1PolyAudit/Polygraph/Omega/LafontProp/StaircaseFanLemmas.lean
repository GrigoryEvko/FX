import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.LafontProp.StaircaseFanLemmas

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.StaircaseFanLemmas — zero-axiom gate
(LAFONT-REPAIR staircase-fan round, supersession file)

Per-declaration zero-axiom gate for the staircase-fan supersession: the four fresh
ascriptions of the fan-core statements, the four fresh Conv fires (mu / delta / crossing /
canonical-reduction) with their soundness consumptions and scale-tower relation-diff pins,
the two refutation-style span-distinctness controls, and the four new true supersession
markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`,
`WellFounded.fix`.  Built by the FX1PolyAudit lib glob; AuditAll registration is a later
round's bookkeeping (AuditAll untouched per this round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfMuFanDuplicationHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfDeltaFanFusionHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfCrossingTwoFanSwapHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfCanonicalReductionHolds
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfMuFanDuplicationFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfMuFanDuplicationFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfMuDuplicatesScaleMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfDeltaFanFusionFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfDeltaFanFusionFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfDeltaFusesScaleMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfCrossingTwoFanSwapFire
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfCrossingTwoFanSwapFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfCrossingSwapsDistinctScalesPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfDistinctScaleTowersStayApart
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfCanonicalReductionFireOnClosedLoop
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfClosedLoopFireDenotesEqually
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfClosedLoopMatrixPin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfClosedLoopVsWirePin
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfClosedLoopVsWireStaysApart
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfHasMuFanDuplication
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfHasDeltaFanFusion
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfHasCrossingTwoFanSwap
#assert_no_axioms FX1Poly.Polygraph.Omega.LafontProp.lsfHasCanonicalReductionOverStrictLayers

end FX1PolyAudit
