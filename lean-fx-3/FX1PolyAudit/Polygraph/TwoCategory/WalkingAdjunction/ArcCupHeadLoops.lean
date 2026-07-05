import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadLoops

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupHeadLoops — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head loops leg (peel campaign H, cup rung 3):
the NON-vacuous typed open-ends discipline at the post-cup seed and the composite fold's
loop freedom along any chained tail.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_cupHeadSeed
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_loops_zero

end FX1PolyAudit
