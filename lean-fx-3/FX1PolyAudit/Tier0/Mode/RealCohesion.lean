import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.RealCohesion

/-! # FX1PolyAudit/AuditTier0ModeRealCohesion — zero-axiom gate for mode-14

Per-declaration zero-axiom gate for `mode-14` (`FX1Poly/Tier0/Mode/RealCohesion.lean`): the fixed-point property
+ the dichotomy (the point has it, `S⁰ ≅ Bool` fails it), the real-cohesion datum + the trivial witness, the
Brouwer statement + its trivial satisfaction, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The fixed-point property + the dichotomy
#assert_no_axioms FX1Poly.Tier0.HasFixedPointProperty
#assert_no_axioms FX1Poly.Tier0.unit_hasFixedPointProperty
#assert_no_axioms FX1Poly.Tier0.bool_not_hasFixedPointProperty

-- Real cohesion + the Brouwer statement
#assert_no_axioms FX1Poly.Tier0.RealCohesion
#assert_no_axioms FX1Poly.Tier0.trivialRealCohesion
#assert_no_axioms FX1Poly.Tier0.RealCohesion.BrouwerStatement
#assert_no_axioms FX1Poly.Tier0.trivialRealCohesion_brouwer

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFullBrouwerTheorem
#assert_no_axioms FX1Poly.Tier0.fxMode_hasNoRetractionPrinciple
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSyntheticRealLine
#assert_no_axioms FX1Poly.Tier0.fxMode_hasShulmanRealCohesiveAxioms

end FX1PolyAudit
