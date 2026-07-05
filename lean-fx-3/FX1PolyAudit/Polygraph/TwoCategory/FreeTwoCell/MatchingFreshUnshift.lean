import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshUnshift

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingFreshUnshift — zero-axiom gate

Per-declaration zero-axiom gate for the two-zone downshift kit (peel campaign H, cup rung
4): the zone equations, both round trips, and the punctured range bound.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.freshUnshiftAbove_ofLe
#assert_no_axioms FX1Poly.Polygraph.freshUnshiftAbove_ofNotLe
#assert_no_axioms FX1Poly.Polygraph.freshUnshiftAbove_ofShifted
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_ofUnshifted
#assert_no_axioms FX1Poly.Polygraph.freshUnshiftAbove_ltTotal

end FX1PolyAudit
