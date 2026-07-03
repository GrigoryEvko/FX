import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeWireSeed

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingRelativeWireSeed — zero-axiom gate

Per-declaration zero-axiom gate for the mid-state wire map and its seed instance (MODE3-D
brick D2): the subtraction-free map, its two read lemmas, both seed-instance forms, and the
honesty marker (the private range read kit is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.relativeWireMap
#assert_no_axioms FX1Poly.Polygraph.relativeWireMap_readsBelow
#assert_no_axioms FX1Poly.Polygraph.relativeWireMap_shiftsAbove
#assert_no_axioms FX1Poly.Polygraph.matchingRelativeWireSim_initial
#assert_no_axioms FX1Poly.Polygraph.matchingRelativeWireSim_initial_ofTracks
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingRelativeWireSeed

end FX1PolyAudit
