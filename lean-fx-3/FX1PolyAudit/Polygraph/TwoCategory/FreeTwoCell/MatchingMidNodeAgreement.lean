import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingMidNodeAgreement

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingMidNodeAgreement — zero-axiom gate

Per-declaration zero-axiom gate for the below-base view agreement of the two renamed folds
(the private appearance scan, port pinning, and port view agreement are covered
transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.belowBaseFoldView_agrees_ofViewSim
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasBelowBaseFoldViewAgreement

end FX1PolyAudit
