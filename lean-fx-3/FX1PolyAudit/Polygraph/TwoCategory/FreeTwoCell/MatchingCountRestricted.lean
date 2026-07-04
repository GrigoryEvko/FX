import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCountRestricted

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingCountRestricted — zero-axiom gate

Per-declaration zero-axiom gate for the node-set-restricted count congruence (the private
restricted join correspondence is covered transitively).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countJoinEventLoops_congrOnNodeSet
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasRestrictedCountCongruence

end FX1PolyAudit
