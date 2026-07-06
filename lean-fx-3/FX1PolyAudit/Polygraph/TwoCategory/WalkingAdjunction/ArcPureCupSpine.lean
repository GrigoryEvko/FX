import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine

/-! # FX1PolyAudit/…/ArcPureCupSpine — zero-axiom gate

Per-declaration zero-axiom gate for the pure-cup regime detector: at the walking adjunction, a
spine with zero total cap tally has every atom carrying cup arity — the entry predicate for the
cap-first reconstruction route's base case.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.allCupArity_ofCapAtomCountZero
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPureCupSpine

end FX1PolyAudit
