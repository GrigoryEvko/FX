import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.DecidableCeilingLedger

/-! # FX1PolyAudit/Tier0/Mode/DecidableCeilingLedger — zero-axiom gate

Per-declaration zero-axiom gate for the three-rung decidability ledger: the wall
marker, the ledger structure and value, and every marker pin.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArbitraryTwoCellUndecidabilityReduction
#assert_no_axioms FX1Poly.Polygraph.DecidableCeilingLedger
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_freeRung_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_freeDecisionUngated_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_saturatedSoundness_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_saturatedCompleteness_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_genericSaturatedRefutation_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_saturatedDecision_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_tierBThin_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_exhibitedConvergent_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_semiThueBridge_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_undecidabilityWall_matchesMarker
#assert_no_axioms FX1Poly.Polygraph.fxDecidableCeiling_generalMarkerSitsAboveLedger

end FX1PolyAudit
