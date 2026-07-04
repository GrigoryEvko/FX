import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedRewriteMatchingInvariance

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedRewriteMatchingInvariance — zero-axiom gate

Per-declaration zero-axiom gate for the matching invariance along the saturated rewrite and
the non-joinability separation principle.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.saturatedReduces_matchingOf_eq_ofGodementInvariant
#assert_no_axioms FX1Poly.Polygraph.saturatedJoinable_matchingOf_eq_ofGodementInvariant
#assert_no_axioms FX1Poly.Polygraph.saturatedRewrite_notJoinable_ofMatchingSeparated
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedRewriteMatchingSeparation

end FX1PolyAudit
