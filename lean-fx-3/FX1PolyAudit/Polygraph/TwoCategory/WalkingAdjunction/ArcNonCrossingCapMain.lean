import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCapMain

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcNonCrossingCapMain — zero-axiom gate

Per-declaration zero-axiom gate for the cap-step preservation of the non-crossing invariant (cap
rung D2a-iv, main theorem): `arcNonCrossing_stepCapArc`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcNonCrossing_stepCapArc

end FX1PolyAudit
