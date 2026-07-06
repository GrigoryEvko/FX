import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingGodementComponent

/-! # FX1PolyAudit/…/SaturatedMatchingGodementComponent — zero-axiom gate

Per-declaration zero-axiom gate for the component-level Godement reduction: the corrected residual
`MatchingGodementSwapRenameableComponent` implies the two-block commutation core `MatchingGodementCommute`
via the component-level extract invariance, free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.matchingGodementCommute_of_swapRenameableComponent
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingGodementCommuteFromComponent

end FX1PolyAudit
