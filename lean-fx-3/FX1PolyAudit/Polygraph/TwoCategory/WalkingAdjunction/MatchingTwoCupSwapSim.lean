import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingTwoCupSwapSim

/-! # FX1PolyAudit/…/MatchingTwoCupSwapSim — zero-axiom gate

Per-declaration zero-axiom gate for brick 2: the cup-bubble `MatchingStepSim` core, POSITIVITY-FREE.  Two
disjoint-window cups fired in the two Godement run orders are `MatchingStepSim (blockSwap nf)`-related over the
plain `WireState` carrier, riding the shipped crux `blockSwap_rootComm` — with NO `0 < nextFresh`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockSwap_map_lowLegs
#assert_no_axioms FX1Poly.Polygraph.blockSwap_map_highLegs
#assert_no_axioms FX1Poly.Polygraph.matchingStepSim_twoCupSwap
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingTwoCupSwapSim

end FX1PolyAudit
