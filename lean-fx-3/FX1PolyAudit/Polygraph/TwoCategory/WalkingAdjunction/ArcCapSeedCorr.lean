import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSeedCorr

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapSeedCorr — zero-axiom gate

Per-declaration zero-axiom gate for the assembled component correspondence at the cap-head
seed (peel campaign H, seed rung, links leg closed at both heads): the cap-seed
`ArcComponentShiftCorr` with degenerate legs and its state-spelled restatement.  The private
degenerate-join computation, event-node avoidance helper, and range plumbing are covered
transitively.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_capHeadSeed
#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_capHeadSeedState

end FX1PolyAudit
