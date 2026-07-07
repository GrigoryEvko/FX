import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.PureCapSurvivorReadoff

/-! # FX1PolyAudit/…/PureCapSurvivorReadoff — zero-axiom gate

Per-declaration zero-axiom gate for brick (2b) closed: the survivor partner read-off.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_survivor_eq_rank
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasPureCapSurvivorReadoff

end FX1PolyAudit
