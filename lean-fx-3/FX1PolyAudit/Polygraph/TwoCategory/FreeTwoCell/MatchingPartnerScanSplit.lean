import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanSplit

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingPartnerScanSplit — zero-axiom gate

Per-declaration zero-axiom gate for the partner-scan structure kit (peel campaign H,
rung E-3, part 2a): skipping a failing head candidate, the two appended-scan splits, and
the mapped-scan pointwise congruence.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_cons_ofTestFails
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_append_ofFrontFails
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_append_ofFoundInFront
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_mapCongr
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_congr_ofTestAgree

end FX1PolyAudit
