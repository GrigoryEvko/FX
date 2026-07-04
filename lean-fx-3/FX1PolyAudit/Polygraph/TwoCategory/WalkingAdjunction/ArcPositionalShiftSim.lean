import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPositionalShiftSim

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPositionalShiftSim — zero-axiom gate

Per-declaration zero-axiom gate for the positional leg of the head-cancellation simulation
(peel campaign H, rung 1): the length transfer, the cup/cap step preservations, the per-atom
dispatch, and the whole-spine fold.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_openWiresLength
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_stepCupArc
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_stepCapArc
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_processArcSpine

end FX1PolyAudit
