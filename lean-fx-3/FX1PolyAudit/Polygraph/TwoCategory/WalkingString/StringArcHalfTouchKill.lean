import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcHalfTouchKill

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcHalfTouchKill — zero-axiom gate
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE substrate)

Per-declaration zero-axiom gate for the half-touch kill and window read-off ported to the adjoint-triple seed.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcHalfTouchContradiction
#assert_no_axioms FX1Poly.Polygraph.stringArcTouchWindowReadsArePair
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcTouchWindowPinning

end FX1PolyAudit
