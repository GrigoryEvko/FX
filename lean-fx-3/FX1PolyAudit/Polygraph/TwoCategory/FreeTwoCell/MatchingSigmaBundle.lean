import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSigmaBundle

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingSigmaBundle — zero-axiom gate

Per-declaration zero-axiom gate for the sigma-witness bundle: the at-or-above preservation of the
block rotation, the `MatchingComponentSim` bundle relating the two transposed Godement run orders
by `blockRotate`, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockRotate_mapsAtOrAboveWithin
#assert_no_axioms FX1Poly.Polygraph.matchingCoreSwap_componentSim_blockRotate
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingComponentSimBundle

end FX1PolyAudit
