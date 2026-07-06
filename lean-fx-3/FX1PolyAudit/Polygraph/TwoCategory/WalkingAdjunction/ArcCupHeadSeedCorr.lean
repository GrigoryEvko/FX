import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadSeedCorr

/-! # FX1PolyAudit/…/ArcCupHeadSeedCorr — zero-axiom gate

Per-declaration zero-axiom gate for the cup-head seed component correspondence:
`isSameComponent_nilEq` (empty-links same-component = equality), `arcCupHead_eventDisconnected` /
`arcCupHead_eventAbsorb` (the event join is invisible to reindexing images), and
`arcComponentShiftCorr_cupHeadSeed` (the seed the whole-spine component fold consumes) must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_nilEq
#assert_no_axioms FX1Poly.Polygraph.arcCupHead_eventDisconnected
#assert_no_axioms FX1Poly.Polygraph.arcCupHead_eventAbsorb
#assert_no_axioms FX1Poly.Polygraph.arcComponentShiftCorr_cupHeadSeed
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCupHeadSeedCorr

end FX1PolyAudit
