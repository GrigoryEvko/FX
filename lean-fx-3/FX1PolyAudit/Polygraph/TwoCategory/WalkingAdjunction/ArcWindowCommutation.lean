import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcWindowCommutation — zero-axiom gate

Per-declaration zero-axiom gate for the disjoint-position wire-op commutation kit: the four
insert/remove commutation laws at separated window positions plus the two append-prefix shift
laws and the position-zero splice rewrite they bottom out in.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_appendPrefix
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_appendPrefix
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_zero
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_insertAbove_commute
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_insertAbove_commute
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_removeAbove_commute
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_removeAbove_commute

end FX1PolyAudit
