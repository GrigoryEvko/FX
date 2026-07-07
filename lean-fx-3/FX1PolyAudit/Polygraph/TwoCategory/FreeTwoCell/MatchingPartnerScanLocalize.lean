import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanLocalize

/-! # FX1PolyAudit/…/MatchingPartnerScanLocalize — zero-axiom gate

Per-declaration zero-axiom gate for the two partner-scan localization duals of the classification half of
the valley-append split: where `findPartnerScan` lands relative to the fresh floor (a genuine member or
the exclude sentinel; the first hit is a real hit; a scan over at-or-above-floor candidates lands
at-or-above the floor).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_result_mem_or_eq_exclude
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_result_passes_of_exists
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_result_ge_of_all_ge
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasPartnerScanLocalize

end FX1PolyAudit
