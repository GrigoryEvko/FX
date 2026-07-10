import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.BridgeDimTwoWithId

/-! # FX1PolyAudit/Polygraph/Omega/BridgeDimTwoWithIdAudit — zero-axiom gate (OMEGA-3 r2, B3).

Per-declaration `#assert_no_axioms` on the re-targeted bridge conv-leg statement over the idCongr sibling
(a forward-declared proposition, defining it introduces no axiom). -/

namespace FX1PolyAudit

-- BridgeDimTwoWithId.lean
#assert_no_axioms FX1Poly.Polygraph.Omega.bridgeDimTwoHoldsWithId

end FX1PolyAudit
