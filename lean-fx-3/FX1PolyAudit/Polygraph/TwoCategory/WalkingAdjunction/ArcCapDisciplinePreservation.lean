import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapDisciplinePreservation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapDisciplinePreservation — zero-axiom gate

Per-declaration zero-axiom gate for the cap preservation of the typed-ends discipline (peel
campaign C, rung 2c): the merged-links transfer and the preservation theorem with its
forced-side analysis.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_oldNodes
#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_stepCapArc

end FX1PolyAudit
