import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCapPreserves

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringFussCatalanCapPreserves — zero-axiom gate (FC-3b, CAP freshness)

Per-declaration zero-axiom gate for the CAP freshness leg of the joint fold invariant: freshness is preserved across a
cap (`StringWireStateFresh_stepCap`).  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringWireStateFresh_stepCap

end FX1PolyAudit
