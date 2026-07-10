import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.SuspensionWithId

/-! # FX1PolyAudit/Polygraph/Omega/SuspensionWithIdAudit — zero-axiom gate (OMEGA-3 r2, B2).

Per-declaration `#assert_no_axioms` on the suspension-preservation fold over the idCongr sibling. -/

namespace FX1PolyAudit

-- SuspensionWithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.suspendPreservesStrictConvWithId

end FX1PolyAudit
