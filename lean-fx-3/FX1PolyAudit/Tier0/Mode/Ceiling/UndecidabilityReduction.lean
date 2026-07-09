import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Ceiling.UndecidabilityReduction

/-! # FX1PolyAudit/Tier0/Mode/Ceiling/UndecidabilityReduction — zero-axiom gate (WP-CEIL-UNDEC ceiling)

Per-declaration zero-axiom gate for the ceiling decidability REDUCTION: the per-instance `Decidable` transport
across the Burroni bridge, the uniform connectedness decider + the forward reduction, the contrapositive wall,
the ceiling marker + its pin, and the involution toy non-vacuity (both discriminating directions).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- The per-instance transport across the bridge
#assert_no_axioms FX1Poly.Polygraph.thueDecidableOfEncodedDecidable

-- The uniform connectedness decider + the forward reduction + the contrapositive wall
#assert_no_axioms FX1Poly.Polygraph.UniformEncodedConnectednessDecider
#assert_no_axioms FX1Poly.Polygraph.uniformEncodedConnectednessDecider_decidesThue
#assert_no_axioms FX1Poly.Polygraph.noUniformConnectednessDecider_ofUndecidableThue

-- The ceiling marker + its pin
#assert_no_axioms FX1Poly.Polygraph.fxCeil_hasUndecidabilityReduction
#assert_no_axioms FX1Poly.Polygraph.fxCeil_hasUndecidabilityReduction_isReduction

-- Toy non-vacuity — the involution as a discriminating point of the FORM-A target
#assert_no_axioms FX1Poly.Polygraph.involutionEncodedConnectedness_positive
#assert_no_axioms FX1Poly.Polygraph.involutionEncodedConnectedness_separation

end FX1PolyAudit
