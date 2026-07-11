import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapHeadLoops

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcCapHeadLoops — zero-axiom gate
(FC-3 r21, THE 110-PERCENT GRIND — the loop-freedom derivation, route B)

Per-declaration zero-axiom gate for the pure-cap cap-head loops leg on the adjoint-triple seed:
the parity-free distinctness invariant, its initial truth and cap-step preservation, the window-pair
loop constancy, the pure-cap chained fold constancy, both capstones, and the anti-vacuity probes.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDistinct_initial
#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDistinct_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_loops_ofDistinct
#assert_no_axioms FX1Poly.Polygraph.processArcSpine_loops_ofPureCapDistinct
#assert_no_axioms FX1Poly.Polygraph.arcFoldLoops_zero_ofPureCapChained
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_loops_zero
#assert_no_axioms FX1Poly.Polygraph.probeCounitUpperLoopsZero
#assert_no_axioms FX1Poly.Polygraph.probeCupThenCapClosesLoop
#assert_no_axioms FX1Poly.Polygraph.probeOutOfRangeCapClosesLoop
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcCapHeadLoopLeg

end FX1PolyAudit
