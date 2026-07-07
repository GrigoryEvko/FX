import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorTopHit

/-! # FX1PolyAudit/…/PureCapSurvivorTopHit — zero-axiom gate

Per-declaration zero-axiom gate for brick (2b) step 2 core: the mapped-range first-hit combinator.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mapAddCompose
#assert_no_axioms FX1Poly.Polygraph.mapRange_cons
#assert_no_axioms FX1Poly.Polygraph.findPartnerScan_mapRange_firstHit
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasPureCapSurvivorTopHit

end FX1PolyAudit
