import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcHeadFoldedSim — zero-axiom gate

Per-declaration zero-axiom gate for the positional correspondence at the folded end states
(peel campaign H, extract-correspondence rung 1): the generic event-count legs of any
positional shift simulation, the folded cup-head and cap-head simulations, and the six
head-specific count/width legs.  The private append-length plumbing is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_cupEventsLength
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_capEventsLength
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_cupHeadFolded
#assert_no_axioms FX1Poly.Polygraph.arcPositionalShiftSim_capHeadFolded
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_cupEventsLength
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_capEventsLength
#assert_no_axioms FX1Poly.Polygraph.arcCupHeadFolded_openWiresLength
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_capEventsLength
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_cupEventsLength
#assert_no_axioms FX1Poly.Polygraph.arcCapHeadFolded_openWiresLength

end FX1PolyAudit
