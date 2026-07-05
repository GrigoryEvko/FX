import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairSeparation

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ArcPairSeparation — zero-axiom gate

Per-declaration zero-axiom gate for the untouched-pair partner separation: the invariant's
symmetry, the unlinked-root and component-separation facts, and the end-state kill (an
untouched pair defeats the partner pin).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ArcPairUntouched.swap
#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_eq_self_ofUnlinked
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_eq_false_ofBothUnlinked
#assert_no_axioms FX1Poly.Polygraph.arcPairUntouched_partnerIndexOf_ne
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPairPartnerSeparation

end FX1PolyAudit
