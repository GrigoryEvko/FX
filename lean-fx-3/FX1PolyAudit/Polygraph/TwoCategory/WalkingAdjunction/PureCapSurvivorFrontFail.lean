import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorFrontFail

/-! # FX1PolyAudit/…/PureCapSurvivorFrontFail — zero-axiom gate

Per-declaration zero-axiom gate for brick (2b) step 1 of the pure-cap survivor readoff: a survivor
bottom port's partner scan drops to the top segment.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_ne_ofUnlinked
#assert_no_axioms FX1Poly.Polygraph.partnerScanFrontTest_false_ofUnlinked
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_survivor_dropsToTop
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasPureCapSurvivorFrontFail

end FX1PolyAudit
