import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingScanFallback

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingScanFallback — zero-axiom gate

Per-declaration zero-axiom gate for the scan fallback and the two-zone shift index
discipline (peel campaign H, cup rung 4): the no-passer fallback, the shift injectivity,
and the window-avoidance facts.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_eqExclude_ofNoPasser
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_two_injective
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_neWindow
#assert_no_axioms FX1Poly.Polygraph.freshShiftAbove_neWindowSucc

end FX1PolyAudit
