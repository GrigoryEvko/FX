import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.BridgeParametricityPayoff

/-! # FX1PolyAudit.Tier0.Mode.BridgeParametricityPayoff — zero-axiom gate (A1-6)

Per-declaration zero-axiom gate for the affine bridge's frontier payoff: Gel as a transpension target, the
bridge's quantifiability, the parametricity-not-cubical positioning, the defuniv gating, the cubical-path
contrast, and the honest recovery-deferred marker. Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.gelIsTranspensionTarget
#assert_no_axioms FX1Poly.Tier0.bridgeMultiplierIsQuantifiable
#assert_no_axioms FX1Poly.Tier0.bridgeSupportsParametricityNotCubical
#assert_no_axioms FX1Poly.Tier0.definitionalUnivalenceGatedByAffineBridge
#assert_no_axioms FX1Poly.Tier0.pathRoutesToCubicalNotParametric
#assert_no_axioms FX1Poly.Tier0.bridgePayoffPositioningOnly_recoveryDeferred

end FX1PolyAudit
