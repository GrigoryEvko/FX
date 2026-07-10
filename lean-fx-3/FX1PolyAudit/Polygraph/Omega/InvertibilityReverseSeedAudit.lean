import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.InvertibilityReverseSeed

/-! # FX1PolyAudit.Polygraph.Omega.InvertibilityReverseSeedAudit — zero-axiom gate for the reverse duality
(OMEGA-6 r2, B3).

Per-declaration `#assert_no_axioms` on the machine-checked refutation of the unconditional reverse duality
(`reverseDuality_unconditional_false`): "folk-invertible ⇒ SN-invertible" is FALSE at the identity-Skolem
placeholder (the object cell is folk-invertible but not SN-invertible). -/

namespace FX1PolyAudit

-- InvertibilityReverseSeed.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.reverseDuality_unconditional_false

end FX1PolyAudit
