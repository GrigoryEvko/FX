import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapNonCrossingJoin

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapNonCrossingJoin — zero-axiom gate (FC-5, P2)

Per-declaration zero-axiom gate for the JOIN-branch CAP non-crossing consumer: the off-window `capRemap` fact and the
uniform cap non-crossing preservation `stringNonCrossing_stepCap` (which consumes the FC-5 P1 boundary census).  Must
be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capRemap_offWindow
#assert_no_axioms FX1Poly.Polygraph.stringNonCrossing_stepCap
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapNonCrossingJoinConsumer

end FX1PolyAudit
