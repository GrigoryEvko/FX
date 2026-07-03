import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingWindowLocality — zero-axiom gate

Per-declaration zero-axiom gate for the prefix half of the wire-window locality: the primitive
splice/removal prefix lemmas (value + range), the per-atom prefix invariant, the spine window predicate
with its fold invariant, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.natListGetAt_natListInsertAt_below
#assert_no_axioms FX1Poly.Tier0.natListInsertAt_length_above
#assert_no_axioms FX1Poly.Tier0.natListGetAt_natListRemoveTwoAt_below
#assert_no_axioms FX1Poly.Tier0.natListRemoveTwoAt_length_above
#assert_no_axioms FX1Poly.Tier0.stepAtom_openWiresPrefix_invariant
#assert_no_axioms FX1Poly.Tier0.processSpine_openWiresPrefix_invariant
#assert_no_axioms FX1Poly.Tier0.composePath_length_left_le
#assert_no_axioms FX1Poly.Tier0.spineDiff_firesAtOrBeyond
#assert_no_axioms FX1Poly.Tier0.spineDiff_firesAtOrBeyond_ownWindow
#assert_no_axioms FX1Poly.Tier0.runMatchingCell_openWiresPrefix_invariant
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingWindowPrefixLocality

end FX1PolyAudit
