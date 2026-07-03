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
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_getAt_bottom
#assert_no_axioms FX1Poly.Polygraph.matchingBoundaryNodes_getAt_top
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_fixesBelow
#assert_no_axioms FX1Poly.Polygraph.rightPadSim_wireRead_inBase
#assert_no_axioms FX1Poly.Polygraph.rightPadSim_wireRead_inPad
#assert_no_axioms FX1Poly.Polygraph.rightPadSim_wireCount
#assert_no_axioms FX1Poly.Polygraph.rightPadSim_padVsShifted_isFalse
#assert_no_axioms FX1Poly.Polygraph.rightPadSim_shiftedVsPad_isFalse
#assert_no_axioms FX1Poly.Polygraph.rightPadSim_padVsPad
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRightPadBoundaryReads

end FX1PolyAudit
