import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingDecisionAssembly

/-! # FX1PolyAudit/…/SaturatedMatchingDecisionAssembly — zero-axiom gate

Per-declaration zero-axiom gate for the assembled fib-3 saturated matching decision: the
unconditional JOIN, the inhabited keystone `SaturatedMatchingCanonicalization`, and the
saturated 2-cell decision must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingReductsShareSpineTrace_holds
#assert_no_axioms FX1Poly.Polygraph.saturatedMatchingCanonicalization_holds
#assert_no_axioms FX1Poly.Polygraph.decideSaturatedTwoCellConv_ofSeed
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedMatchingDecisionAssembled

end FX1PolyAudit
