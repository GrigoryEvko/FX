import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeWireSim

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRelativeWireSim — zero-axiom gate

Per-declaration zero-axiom gate for the relative-run wire simulation (MODE3-D brick D1): the
correspondence structure, the cup/cap/atom step preservations, the disciplined fold, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.MatchingRelativeWireSim
#assert_no_axioms FX1Poly.Polygraph.matchingRelativeWireSim_stepCup
#assert_no_axioms FX1Poly.Polygraph.matchingRelativeWireSim_stepCap
#assert_no_axioms FX1Poly.Polygraph.matchingRelativeWireSim_stepAtom
#assert_no_axioms FX1Poly.Polygraph.matchingRelativeWireSim_processSpine
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRelativeWireSim

end FX1PolyAudit
