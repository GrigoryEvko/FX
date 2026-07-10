import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedGeneralBricks

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedGeneralBricks — zero-axiom gate

Per-declaration zero-axiom gate for the GENERIC-NATIVE general-width bricks (POLY-TAB r4): the cast helpers +
`whiskerLeftCanonGen` + `gadgetSplitRightGen`.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.castBoundaryCongrGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.ofCastLeftGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompCastLeftExtrudeGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftCanonGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gadgetSplitRightGenZero
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gadgetSplitRightGenOne
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerRightLeftBraidGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.gadgetSplitRightGen

end FX1PolyAudit
