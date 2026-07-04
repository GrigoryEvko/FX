import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCongruenceProved

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SaturatedMatchingCongruenceProved — zero-axiom gate

Per-declaration zero-axiom gate for the proved four-field matching compositionality bundle
and the congruence-discharged saturated soundness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingSaturatedCongruence_proved
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_matchingOf_eq_ofGodementInvariant
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingSaturatedCongruence

end FX1PolyAudit
