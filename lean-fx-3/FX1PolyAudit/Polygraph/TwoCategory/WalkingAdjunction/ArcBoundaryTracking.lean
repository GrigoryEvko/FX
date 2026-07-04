import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcBoundaryTracking — zero-axiom gate

Per-declaration zero-axiom gate for the arc fold's boundary tracking: the open-wire count
follows the chained boundary through cup/cap steps, and the walking-adjunction seed discharges
the arity hypothesis wholesale.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natSumRightCancel
#assert_no_axioms FX1Poly.Polygraph.stepArcAtom_openWires_tracksBoundary
#assert_no_axioms FX1Poly.Polygraph.adjunctionSpineAtom_hasCupOrCapArity

end FX1PolyAudit
