import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingFreshShift — zero-axiom gate

Per-declaration zero-axiom gate for the fresh-shift equivariance of the matching fold's wire view: the
shift renaming with its two evaluation lemmas, the per-atom cup/cap equivariance, the whole-block fold
equivariance, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_ofLe
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_ofNotLe
#assert_no_axioms FX1Poly.Polygraph.stepAtom_wireView_freshShift
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_wireView_freshShift
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_map_inRange
#assert_no_axioms FX1Poly.Polygraph.natListEqOfPointwiseGetAt
#assert_no_axioms FX1Poly.Polygraph.mapFixedBelow
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_append_inside
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_natListInsertAt_inside
#assert_no_axioms FX1Poly.Polygraph.stepAtomPair_windowWireView_freshShift
#assert_no_axioms FX1Poly.Polygraph.runMatchingCell_windowWireView_freshShift
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingFreshShiftEquivariance
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingWindowFreshShiftCongruence

end FX1PolyAudit
