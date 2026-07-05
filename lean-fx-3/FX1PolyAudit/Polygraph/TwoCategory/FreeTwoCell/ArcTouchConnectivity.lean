import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTouchConnectivity

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ArcTouchConnectivity — zero-axiom gate

Per-declaration zero-axiom gate for the touch-connectivity kit: the fold's append refolding,
the component-test/root-equality conversions, the cap's fresh bump, the event's reach to
either touched read, and the singleton-component kill.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.processArcSpine_append
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_eq_ofSameComponent
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_ofRootEq
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_nextFresh
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_eventSecondRead
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_eventTouchedNode
#assert_no_axioms FX1Poly.Polygraph.eq_ofSameComponent_ofUnlinked
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcTouchConnectivityKit

end FX1PolyAudit
