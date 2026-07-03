import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeZone

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRelativeZone — zero-axiom gate

Per-declaration zero-axiom gate for the mid-state wire map's zone discipline: the two zone
bounds, the injectivity theorem, the bundle with its builders, and the mid-state
instantiation (the private cancellation kit is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.relativeWireMap_portImageBelow
#assert_no_axioms FX1Poly.Polygraph.relativeWireMap_freshImageAtOrAbove
#assert_no_axioms FX1Poly.Polygraph.relativeWireMap_isInjective
#assert_no_axioms FX1Poly.Polygraph.RelativeWireZoneDiscipline
#assert_no_axioms FX1Poly.Polygraph.relativeWireZoneDiscipline_ofFreshDistinct
#assert_no_axioms FX1Poly.Polygraph.relativeWireZoneDiscipline_ofState
#assert_no_axioms FX1Poly.Polygraph.relativeWireZoneDiscipline_ofMidState
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasRelativeWireZoneDiscipline

end FX1PolyAudit
