import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapWindowSeedReadoff

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapWindowSeedReadoff — zero-axiom gate

Per-declaration zero-axiom gate for the seed read-off: the located-cap certificate over a
boundary-chained spine yields the bubble witness with the moved cap pinned to the
certificate's window position on the seed boundary.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_alongArcSpine
#assert_no_axioms FX1Poly.Polygraph.bubblesToFront_ofArcPairCapWindow
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCapWindowSeedReadoff

end FX1PolyAudit
