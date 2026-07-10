import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcArity — zero-axiom gate (FC-3 item 1 foundation)

Per-declaration zero-axiom gate for the four-generator cup/cap arity dispatch: the seed classification, the
`AtomHasCupOrCapArity` delegate, the two non-vacuity smokes (a unit lands a cup, a counit lands a cap), and the
honesty marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjointTripleSpineAtom_isCupOrCap
#assert_no_axioms FX1Poly.Polygraph.adjointTripleSpineAtom_hasCupOrCapArity
#assert_no_axioms FX1Poly.Polygraph.stringUnitLowerSpineAtom_isCup
#assert_no_axioms FX1Poly.Polygraph.stringCounitUpperSpineAtom_isCap
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcArityDispatch

end FX1PolyAudit
