import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcSwapPeel

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcSwapPeel — zero-axiom gate (FC-3 item 1)

Per-declaration zero-axiom gate for the arc-preservation peel at the walking adjoint triple (arc extraction invariant
along `AtomicTraceEquiv`) and its honesty marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractArc_eq_of_stringAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcTraceEquivExtraction

end FX1PolyAudit
