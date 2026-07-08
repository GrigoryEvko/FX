import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingSwapPeel

/-! # FX1PolyAudit/…/MatchingSwapPeel — zero-axiom gate

Per-declaration zero-axiom gate for Track B piece (a): the matching-carrier fold-through peel.  Along any
`AtomicTraceEquiv` between pure-cup spines the width-0 matching extract is invariant — the swap node rides
brick 2 (`matchingStepSim_twoCupSwap`, positivity-free) and the sentinel-free component fold, never
`0 < nextFresh` / `sigma 0 = 0`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.blockSwap_fix_ge
#assert_no_axioms FX1Poly.Polygraph.matchingComponentSim_ofStepSim
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_eq_of_atomicCupSwap
#assert_no_axioms FX1Poly.Polygraph.extractDiagram_eq_of_atomicPureCupTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasMatchingSwapPeel

end FX1PolyAudit
