import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescGodement

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescGodement — zero-axiom gate (WAVE-1 keystone)

Per-declaration zero-axiom gate for the disjoint-window Godement / interchange independence over the generic
`WiringDesc` engine: the state-parametric `nextFresh` commutation, the freshness predicate + its seed anchor, the
concrete disjoint-window interchange soundness smokes (cup / cap / crossing pairs), the freshness-gate
refutation, the freshness-conditioned residual, and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the state-parametric nextFresh commutation
#assert_no_axioms FX1Poly.Polygraph.stepWiring_nextFresh
#assert_no_axioms FX1Poly.Polygraph.disjointWindow_nextFresh_commute

-- freshness predicate + seed anchor
#assert_no_axioms FX1Poly.Polygraph.WiringDescStateFresh
#assert_no_axioms FX1Poly.Polygraph.wiringDescStateFresh_fourWireSeed

-- the four-wire seed
#assert_no_axioms FX1Poly.Polygraph.fourWireSeed
#assert_no_axioms FX1Poly.Polygraph.fourWireSeed_eq_seed

-- concrete disjoint-window interchange soundness (cup / cap)
#assert_no_axioms FX1Poly.Polygraph.disjointWindow_capCap_commute
#assert_no_axioms FX1Poly.Polygraph.disjointWindow_cupCap_commute

-- crossing ∥ cap, staged
#assert_no_axioms FX1Poly.Polygraph.crossingCapAfterCrossing
#assert_no_axioms FX1Poly.Polygraph.crossingCapOrderA
#assert_no_axioms FX1Poly.Polygraph.crossingCapAfterCap
#assert_no_axioms FX1Poly.Polygraph.crossingCapOrderB
#assert_no_axioms FX1Poly.Polygraph.crossingCap_stepA1
#assert_no_axioms FX1Poly.Polygraph.crossingCap_stepA2
#assert_no_axioms FX1Poly.Polygraph.crossingCap_stepB1
#assert_no_axioms FX1Poly.Polygraph.crossingCap_stepB2
#assert_no_axioms FX1Poly.Polygraph.disjointWindow_crossingCap_commute

-- crossing ∥ cup, staged
#assert_no_axioms FX1Poly.Polygraph.crossingCupAfterCup
#assert_no_axioms FX1Poly.Polygraph.crossingCupOrderA
#assert_no_axioms FX1Poly.Polygraph.crossingCupAfterCrossing
#assert_no_axioms FX1Poly.Polygraph.crossingCupOrderB
#assert_no_axioms FX1Poly.Polygraph.crossingCup_stepA1
#assert_no_axioms FX1Poly.Polygraph.crossingCup_stepA2
#assert_no_axioms FX1Poly.Polygraph.crossingCup_stepB1
#assert_no_axioms FX1Poly.Polygraph.crossingCup_stepB2
#assert_no_axioms FX1Poly.Polygraph.disjointWindow_crossingCup_commute

-- the freshness-gate refutation
#assert_no_axioms FX1Poly.Polygraph.freshnessAdversaryState
#assert_no_axioms FX1Poly.Polygraph.disjointWindow_extract_differs_withoutFreshness

-- the freshness-conditioned residual
#assert_no_axioms FX1Poly.Polygraph.WiringDescDisjointWindowFresh

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDisjointWindowNextFreshCommute
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDisjointWindowConcreteSoundness
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDisjointWindowUnconditionalRefuted
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescDisjointWindowFreshProof

end FX1PolyAudit
