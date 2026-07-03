import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadSeed

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingLeftPadSeed — zero-axiom gate

Per-declaration zero-axiom gate for the left-pad seed instance: the pad-prefix range split,
the canonical-seed left-pad simulation, and the honesty marker (the private range/append
read kit is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.leftPaddedRangeSplit
#assert_no_axioms FX1Poly.Polygraph.matchingLeftPadSim_initial
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingLeftPadSeed

end FX1PolyAudit
