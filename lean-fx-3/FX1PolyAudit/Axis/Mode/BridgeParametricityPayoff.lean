import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.BridgeParametricityPayoff

/-! # FX1PolyAudit.Axis.Mode.BridgeParametricityPayoff — zero-axiom gate (A1-6)

Per-declaration zero-axiom gate for the affine bridge's frontier payoff: Gel as a transpension target, the
bridge's quantifiability, the parametricity-not-cubical positioning, the defuniv gating, the cubical-path
contrast, and the honest recovery-deferred marker. Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.gelIsTranspensionTarget
#assert_no_axioms FX1Poly.Axis.bridgeMultiplierIsQuantifiable
#assert_no_axioms FX1Poly.Axis.bridgeSupportsParametricityNotCubical
#assert_no_axioms FX1Poly.Axis.definitionalUnivalenceGatedByAffineBridge
#assert_no_axioms FX1Poly.Axis.pathRoutesToCubicalNotParametric
#assert_no_axioms FX1Poly.Axis.bridgePayoffPositioningOnly_recoveryDeferred

end FX1PolyAudit
