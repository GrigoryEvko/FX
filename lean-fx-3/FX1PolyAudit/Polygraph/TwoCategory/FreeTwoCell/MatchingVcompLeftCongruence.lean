import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingVcompLeftCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the vcomp-LEFT matching congruence: the run-composition
law, the fold-append split, the seed-generic core, the walking-adjunction field inhabitant,
and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spine_vcomp
#assert_no_axioms FX1Poly.Polygraph.processSpine_append
#assert_no_axioms FX1Poly.Polygraph.extractAfterProcessing_vcompLeft_ofSeed
#assert_no_axioms FX1Poly.Polygraph.matchingOf_vcompLeft_congruence
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingVcompLeftCongruence

end FX1PolyAudit
