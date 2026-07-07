import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCupWindowScanSplit

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCupWindowScanSplit — zero-axiom gate

Per-declaration zero-axiom gate for the single-cup partner-scan window split: the assembled
scan equation that a cup-window composite partner scan is the index shift of the fresh partner scan.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_range_cupWindowSplit
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_range_frontSegmentMisses

end FX1PolyAudit
