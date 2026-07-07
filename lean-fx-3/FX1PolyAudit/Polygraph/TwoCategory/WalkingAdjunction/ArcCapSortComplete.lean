import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSortComplete

/-! # FX1PolyAudit/…/ArcCapSortComplete — zero-axiom gate

Per-declaration zero-axiom gate for pure-cap completeness `pureCapSpine_sort` (the peel-first mirror
of #2184): two boundary-chained pure-cap spines over a bottom boundary with equal arc structure are
`SpineTraceEquiv`.  The private fuel driver and the count reflections are covered transitively — a
`propext` leak in any would surface on the public theorems asserted here.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.allCapArity_ofArcEqualToPureCap
#assert_no_axioms FX1Poly.Polygraph.pureCapSpines_sameLength_ofArcEqual
#assert_no_axioms FX1Poly.Polygraph.pureCapSpine_sort_nil
#assert_no_axioms FX1Poly.Polygraph.pureCapSpine_sort
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCapSortComplete

end FX1PolyAudit
