import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcOpenEndsDiscipline

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcOpenEndsDiscipline — zero-axiom gate

Per-declaration zero-axiom gate for the typed-ends discipline statement layer (peel campaign C,
rung 2a): the two-shift parity stability, the cup/cap window pins, and the discipline's truth
at the fresh seed state.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.adjunctionModeAtDistance_stableUnderTwoShift
#assert_no_axioms FX1Poly.Polygraph.adjunctionCupAtom_windowPositionMode
#assert_no_axioms FX1Poly.Polygraph.adjunctionCapAtom_windowPositionMode
#assert_no_axioms FX1Poly.Polygraph.arcOpenEndsDiscipline_initial

end FX1PolyAudit
