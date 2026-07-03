import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSeed

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRightPadSeed — zero-axiom gate

Per-declaration zero-axiom gate for the right-pad seed instance: the shift's boolean-equality
reflection, the pad suffix with its length/read characterizations, the padded-range split, the
canonical seed with its `matchingOfSpineList` read-off, the initial pad-simulation, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_beqCongr
#assert_no_axioms FX1Poly.Polygraph.padIdentifiers
#assert_no_axioms FX1Poly.Polygraph.padIdentifiers_length
#assert_no_axioms FX1Poly.Polygraph.padIdentifiers_getAt
#assert_no_axioms FX1Poly.Polygraph.paddedRangeSplit
#assert_no_axioms FX1Poly.Polygraph.canonicalMatchingSeed
#assert_no_axioms FX1Poly.Polygraph.matchingOfSpineList_ofCanonicalSeed
#assert_no_axioms FX1Poly.Polygraph.matchingRightPadSim_initial
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRightPadSeed

end FX1PolyAudit
