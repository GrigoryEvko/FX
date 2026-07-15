import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.BridgeIntervalAffineMultiplier

/-! # FX1PolyAudit.Axis.Mode.BridgeIntervalAffineMultiplier — zero-axiom gate (A1-5)

Per-declaration zero-axiom gate for the bridge (affine) vs path (cubical) interval structure-class split: the two
named multipliers, their classifications, the reversal/connections/diagonal distinctions, the refinement, and the
distinctness. Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.bridgeIntervalMultiplier
#assert_no_axioms FX1Poly.Axis.pathIntervalMultiplier
#assert_no_axioms FX1Poly.Axis.bridgeIntervalMultiplier_isAffine
#assert_no_axioms FX1Poly.Axis.pathIntervalMultiplier_isDeMorgan
#assert_no_axioms FX1Poly.Axis.bridgeLacksReversal_pathHasReversal
#assert_no_axioms FX1Poly.Axis.bridgeLacksConnections
#assert_no_axioms FX1Poly.Axis.bridgeLacksDiagonal
#assert_no_axioms FX1Poly.Axis.bridgeRefinesPath
#assert_no_axioms FX1Poly.Axis.bridgeIntervalMultiplier_ne_pathIntervalMultiplier
#assert_no_axioms FX1Poly.Axis.pathDoesNotRefineBridge

end FX1PolyAudit
