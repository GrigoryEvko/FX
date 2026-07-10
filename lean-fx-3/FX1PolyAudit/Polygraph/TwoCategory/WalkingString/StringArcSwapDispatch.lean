import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcSwapDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcSwapDispatch — zero-axiom gate (FC-3 item 1 producer)

Per-declaration zero-axiom gate for the four-generator atom-level swap-core dispatcher (16 arms routing to the four
generic builders) and its honesty marker.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringArcSwapCorePackage_of_stringSwap
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcSwapDispatch

end FX1PolyAudit
