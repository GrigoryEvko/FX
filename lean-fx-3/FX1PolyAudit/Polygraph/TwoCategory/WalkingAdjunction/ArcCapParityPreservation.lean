import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapParityPreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapParityPreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cap step's preservation of the opposite-class
strand-endpoint invariant: the class-stable window backmap and the join dispatch.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcEndTokenClass_capBackmap
#assert_no_axioms FX1Poly.Polygraph.arcEndTokenParity_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCapParityPreservation

end FX1PolyAudit
