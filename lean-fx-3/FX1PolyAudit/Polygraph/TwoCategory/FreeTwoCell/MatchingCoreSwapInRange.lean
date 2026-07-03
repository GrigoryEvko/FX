import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCoreSwapInRange

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCoreSwapInRange — zero-axiom gate

Per-declaration zero-axiom gate for the in-range component core swap: the full
`MatchingGodementComponentCoreSwap`-body discharge under the in-range/cup-cap premises, and the
honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingGodementComponentCoreSwap_ofInRange
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingCoreSwapInRangeWitness

end FX1PolyAudit
