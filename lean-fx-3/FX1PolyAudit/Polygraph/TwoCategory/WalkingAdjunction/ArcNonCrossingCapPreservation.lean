import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCapPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingCapPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cap-step position infrastructure (cap rung D2a-iv, part 1):
the shrunk open-wire length, the window slots' adjacency, the surviving-token node bound, and the
window backmap's monotone position remap.  The private clean Nat-subtraction plumbing and the
`freshShiftAbove` monotonicity helper are covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapNewOpenLength
#assert_no_axioms FX1Poly.Polygraph.arcCapWindowAdjacent
#assert_no_axioms FX1Poly.Polygraph.arcCapNodeBelow
#assert_no_axioms FX1Poly.Polygraph.arcCapOldPositionMonotone
#assert_no_axioms FX1Poly.Polygraph.arcCapBackmapPositionOffWindow

end FX1PolyAudit
