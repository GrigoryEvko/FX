import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingStaircaseReduction

/-! # FX1PolyAudit/…/SaturatedMatchingStaircaseReduction — zero-axiom gate

Per-declaration zero-axiom gate for the matching-carrier completeness reduction: the reduction
`convOfMapEq_ofCanonicalMatchingStaircase` and the whole-keystone capstone
`saturatedMatchingCanonicalization_ofMatchingStaircase` (which additionally consumes the shipped
boundary-disciplined soundness + `matchingSaturatedCongruence_proved`) must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` — so the capstone's zero-axiom
pass also witnesses the soundness chain it composes over is clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.convOfMapEq_ofCanonicalMatchingStaircase
#assert_no_axioms FX1Poly.Polygraph.saturatedMatchingCanonicalization_ofMatchingStaircase
#assert_no_axioms FX1Poly.Polygraph.canonicalMatchingStaircaseData_of
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasKeystoneReducedToMatchingReconstruction

end FX1PolyAudit
