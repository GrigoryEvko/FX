import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadSim

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingLeftPadSim — zero-axiom gate

Per-declaration zero-axiom gate for the left-padded matching simulation: the cup/cap step
preservations at the prefix-offset window and the honesty marker (the private prefix-surgery,
zone-adapter, and two-position cap lemmas are covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingLeftPadSim_stepCup
#assert_no_axioms FX1Poly.Polygraph.matchingLeftPadSim_stepCap
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingLeftPadSim

end FX1PolyAudit
