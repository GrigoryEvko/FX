import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadLoops

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapHeadLoops — zero-axiom gate

Per-declaration zero-axiom gate for the composite cap-head loops leg (peel campaign H,
rung E-3, part 7): the post-cap seed satisfies the typed-ends discipline vacuously, and
the composite fold over the remaining chained atoms never closes a loop.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_capHeadSeed
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_loops_zero

end FX1PolyAudit
