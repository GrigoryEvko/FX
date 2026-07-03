import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpinePositionShift

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpinePositionShift — zero-axiom gate

Per-declaration zero-axiom gate for the left-whisker spine correspondence: the pointwise
position-shift relation, the `spineDiff` master over `delta`-gapped left accumulators, the
`whiskerLeft` payoff instance, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpinePositionShifted
#assert_no_axioms FX1Poly.Polygraph.spineDiff_spinePositionShifted
#assert_no_axioms FX1Poly.Polygraph.spine_whiskerLeft_spinePositionShifted
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpinePositionShift

end FX1PolyAudit
