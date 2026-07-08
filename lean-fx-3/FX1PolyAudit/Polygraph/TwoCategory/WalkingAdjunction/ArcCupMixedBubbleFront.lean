import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedBubbleFront

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupMixedBubbleFront — zero-axiom gate

Per-declaration zero-axiom gate for mixed cup-fronting: the purity-free bubble realization
(`AtomicTraceEquiv` + arc-preservation over a mixed cup/cap spine) and the census-located
cup-fronting object from a positive cup total.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.bubbleCupToFrontMixed
#assert_no_axioms FX1Poly.Polygraph.arcCupMixedFrontsCup_ofCupCountPos

end FX1PolyAudit
