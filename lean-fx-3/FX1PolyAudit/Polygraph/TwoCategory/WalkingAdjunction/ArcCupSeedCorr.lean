import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSeedCorr

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupSeedCorr — zero-axiom gate

Per-declaration zero-axiom gate for the assembled component correspondence at the cup-head
seed (peel campaign H, seed rung, links leg closed at the cup): the seed
`ArcComponentShiftCorr` and its state-spelled restatement.  The private event-node
component-avoidance helper is covered transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_cupHeadSeed
#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_cupHeadSeedState

end FX1PolyAudit
