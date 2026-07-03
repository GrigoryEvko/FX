import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingEmptyBoundary

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingEmptyBoundary — zero-axiom gate

Per-declaration zero-axiom gate for the empty-boundary soundness capstone: the counter-shift
proxy chain, the all-boundaries total capstone, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingOf_sound_ofCupCapCells_emptyBoundary
#assert_no_axioms FX1Poly.Polygraph.matchingOf_sound_ofCupCapCells_allBoundaries
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingSoundnessAllBoundaries

end FX1PolyAudit
