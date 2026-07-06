import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingFold

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPerfectMatchingFold — zero-axiom gate

Per-declaration zero-axiom gate for the whole-spine fold of the token-frame perfect matching (noFixedPoint
rung): the per-atom step, the chained-spine transport, and the canonical-seed capstone.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcPerfectMatchingTokens_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcPerfectMatchingTokens_processArcSpine_ofChained
#assert_no_axioms FX1Poly.Polygraph.arcPerfectMatchingTokens_ofChainedSpineList

end FX1PolyAudit
