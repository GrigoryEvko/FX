import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSim

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRightPadSim — zero-axiom gate

Per-declaration zero-axiom gate for the right-padded matching simulation: the suffix-aware
insertion/removal surgery, the shift's pad-zone avoidance, the two join-inertness lemmas,
the cup/cap step preservations, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_append_left
#assert_no_axioms FX1Poly.Polygraph.natListRemoveTwoAt_append_left
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_avoidsPadZone
#assert_no_axioms FX1Poly.Polygraph.padRootsFixed_unionFindJoin
#assert_no_axioms FX1Poly.Polygraph.rootAvoidsPadZone_unionFindJoin
#assert_no_axioms FX1Poly.Polygraph.matchingRightPadSim_stepCup
#assert_no_axioms FX1Poly.Polygraph.matchingRightPadSim_stepCap
#assert_no_axioms FX1Poly.Polygraph.matchingRightPadSim_step_ofInRange
#assert_no_axioms FX1Poly.Polygraph.matchingRightPadSim_processSpine_ofBoundaryDiscipline
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRightPadSimSteps

end FX1PolyAudit
