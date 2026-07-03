import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingLeftPadFold — zero-axiom gate

Per-declaration zero-axiom gate for the left-padded two-list fold: the corresponded-pair
step dispatch, the boundary-disciplined fold over a position-shifted spine pair, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingLeftPadSim_step_ofCorrespondence
#assert_no_axioms FX1Poly.Polygraph.matchingLeftPadSim_processSpine_ofCorrespondence
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingLeftPadFold

end FX1PolyAudit
