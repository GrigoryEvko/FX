import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRangeInterleave — zero-axiom gate

Per-declaration zero-axiom gate for the cap-window candidate interleave (peel campaign H,
rung E-3, part 2b): the generic range split, the all-failing-segment scan lemmas, and the
two window decompositions of the candidate ranges.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.rangeSplit
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_eqExclude_ofAllFail
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_dropMiddle_ofAllFail
#assert_no_axioms FX1Poly.Polygraph.rangeInterleaveAtWindow
#assert_no_axioms FX1Poly.Polygraph.rangeShiftImageAtWindow

end FX1PolyAudit
