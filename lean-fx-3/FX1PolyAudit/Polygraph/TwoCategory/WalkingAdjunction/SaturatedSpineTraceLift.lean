import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedSpineTraceLift

/-! # FX1PolyAudit/…/SaturatedSpineTraceLift — zero-axiom gate

Per-declaration zero-axiom gate for the free-trace lift into the saturated relation and the
existence-factored keystone reduction: the lift `SaturatedTwoCellConv.ofSpineTraceEquiv`
(`SpineTraceEquiv` of spines ⟹ `SaturatedTwoCellConv`, via `twoCellConvFull_ofSpineTraceEquiv` then
`ofFull`), the reduction `convOfMapEq_ofMatchingReductsShareSpineTrace`, and the whole-keystone capstone
`saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace` must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` — so the capstone's zero-axiom pass
also witnesses the shipped free reconstruction and boundary-disciplined soundness it composes over are
clean. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellConv.ofSpineTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.convOfMapEq_ofMatchingReductsShareSpineTrace
#assert_no_axioms FX1Poly.Polygraph.saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineTraceLiftIntoSaturated

end FX1PolyAudit
