import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapWindowCounts

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapWindowCounts — zero-axiom gate

Per-declaration zero-axiom gate for the consumed strand's event counts (peel campaign H,
rung E-3, part 9): the peeled cap's strand carries exactly one cap event and no cup event
at the composite end state, and the right window port reads the same strand.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowStrandCapCount
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowStrandCupCount
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_windowRightRootEq

end FX1PolyAudit
