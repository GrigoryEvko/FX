import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSpineActionCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingSpineActionCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the spine-shape action congruence: the shape action, its
definitional read-off, the per-atom shape congruence, the difference-list left-length
congruence, the right-whisker action invisibility, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingShapeAction
#assert_no_axioms FX1Poly.Polygraph.stepAtom_eq_matchingShapeAction
#assert_no_axioms FX1Poly.Polygraph.stepAtom_congrOfShape
#assert_no_axioms FX1Poly.Polygraph.processSpine_spineDiff_congrOfLeftLength
#assert_no_axioms FX1Poly.Polygraph.processSpine_spine_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingSpineActionCongruence

end FX1PolyAudit
