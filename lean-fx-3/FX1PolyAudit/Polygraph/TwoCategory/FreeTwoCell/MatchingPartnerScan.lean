import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingPartnerScan — zero-axiom gate

Per-declaration zero-axiom gate for the partner-scan semantics kit: the cons unfold, scan
soundness, scan completeness, the exclude-agreement trichotomy, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_cons
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_root_ofFound
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_neExclude_ofTarget
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_excludeAgree
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingPartnerScanKit

end FX1PolyAudit
