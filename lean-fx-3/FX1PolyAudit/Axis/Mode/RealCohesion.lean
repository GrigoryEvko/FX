import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.RealCohesion

/-! # FX1PolyAudit/AuditAxisModeRealCohesion — zero-axiom gate for mode-14

Per-declaration zero-axiom gate for `mode-14` (`FX1Poly/Axis/Mode/RealCohesion.lean`): the fixed-point property
+ the dichotomy (the point has it, `S⁰ ≅ Bool` fails it), the real-cohesion datum + the trivial witness, the
Brouwer statement + its trivial satisfaction, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The fixed-point property + the dichotomy
#assert_no_axioms FX1Poly.Axis.HasFixedPointProperty
#assert_no_axioms FX1Poly.Axis.unit_hasFixedPointProperty
#assert_no_axioms FX1Poly.Axis.bool_not_hasFixedPointProperty

-- Real cohesion + the Brouwer statement
#assert_no_axioms FX1Poly.Axis.RealCohesion
#assert_no_axioms FX1Poly.Axis.trivialRealCohesion
#assert_no_axioms FX1Poly.Axis.RealCohesion.BrouwerStatement
#assert_no_axioms FX1Poly.Axis.trivialRealCohesion_brouwer

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasFullBrouwerTheorem
#assert_no_axioms FX1Poly.Axis.fxMode_hasNoRetractionPrinciple
#assert_no_axioms FX1Poly.Axis.fxMode_hasSyntheticRealLine
#assert_no_axioms FX1Poly.Axis.fxMode_hasShulmanRealCohesiveAxioms

end FX1PolyAudit
