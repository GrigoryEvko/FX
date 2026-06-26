import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.BridgeIntervalAffineMultiplier

/-! # FX1PolyAudit.Tier0.Mode.BridgeIntervalAffineMultiplier — zero-axiom gate (A1-5)

Per-declaration zero-axiom gate for the bridge (affine) vs path (cubical) interval structure-class split: the two
named multipliers, their classifications, the reversal/connections/diagonal distinctions, the refinement, and the
distinctness. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.bridgeIntervalMultiplier
#assert_no_axioms FX1Poly.Tier0.pathIntervalMultiplier
#assert_no_axioms FX1Poly.Tier0.bridgeIntervalMultiplier_isAffine
#assert_no_axioms FX1Poly.Tier0.pathIntervalMultiplier_isDeMorgan
#assert_no_axioms FX1Poly.Tier0.bridgeLacksReversal_pathHasReversal
#assert_no_axioms FX1Poly.Tier0.bridgeLacksConnections
#assert_no_axioms FX1Poly.Tier0.bridgeLacksDiagonal
#assert_no_axioms FX1Poly.Tier0.bridgeRefinesPath
#assert_no_axioms FX1Poly.Tier0.bridgeIntervalMultiplier_ne_pathIntervalMultiplier
#assert_no_axioms FX1Poly.Tier0.pathDoesNotRefineBridge

end FX1PolyAudit
