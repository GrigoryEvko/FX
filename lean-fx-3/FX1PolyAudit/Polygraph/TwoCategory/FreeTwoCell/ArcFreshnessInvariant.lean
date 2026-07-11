import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshnessInvariant

/-! # FX1PolyAudit … ArcFreshnessInvariant — zero-axiom gate (mode-3 floor, MODE-COMMUTE truth-probes)

Per-declaration zero-axiom gate for the freshness-invariant truth-probes: the seed satisfies the reachable bundle
(`arcSeedThreeIsFresh` / `arcSeedThreeIsForest` / `arcSeedThreeIsNonDegenerate`), the r2 adversarial state violates
freshness and diverges (`refuteAdversarialState_violatesFresh` / `arcAdversarialBoundaryDiverges`), freshness does
not imply forest (`arcFreshCyclicState` / `arcFreshCyclicState_isFresh` / `arcFreshCyclicLinks_notForest`), and the
gated commute holds on a concrete reachable slack-fresh forest state (`arcSlackForestState` /
`arcSlackForestState_isFresh` / `arcSlackForestState_isForest` / `arcSlackRedexState` / `arcSlackReductState` /
`arcSlackForestPartitionComponentsAgree`), plus the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  The project
`#assert_no_axioms` macro is fuel-based, so each declaration is ALSO checked by the exhaustive core `#print axioms`.
NOT registered in `AuditAll` here (the orchestrator does the unified registration in one breath). -/

namespace FX1PolyAudit

-- positive control: the seed satisfies the reachable bundle
#assert_no_axioms FX1Poly.Polygraph.arcSeedThreeIsFresh
#print axioms FX1Poly.Polygraph.arcSeedThreeIsFresh
#assert_no_axioms FX1Poly.Polygraph.arcSeedThreeIsForest
#print axioms FX1Poly.Polygraph.arcSeedThreeIsForest
#assert_no_axioms FX1Poly.Polygraph.arcSeedThreeIsNonDegenerate
#print axioms FX1Poly.Polygraph.arcSeedThreeIsNonDegenerate

-- negative control: the r2 adversarial state violates freshness and diverges
#assert_no_axioms FX1Poly.Polygraph.refuteAdversarialState_violatesFresh
#print axioms FX1Poly.Polygraph.refuteAdversarialState_violatesFresh
#assert_no_axioms FX1Poly.Polygraph.arcAdversarialBoundaryDiverges
#print axioms FX1Poly.Polygraph.arcAdversarialBoundaryDiverges

-- the dividing line: freshness does not imply forest
#assert_no_axioms FX1Poly.Polygraph.arcFreshCyclicState
#print axioms FX1Poly.Polygraph.arcFreshCyclicState
#assert_no_axioms FX1Poly.Polygraph.arcFreshCyclicState_isFresh
#print axioms FX1Poly.Polygraph.arcFreshCyclicState_isFresh
#assert_no_axioms FX1Poly.Polygraph.arcFreshCyclicLinks_notForest
#print axioms FX1Poly.Polygraph.arcFreshCyclicLinks_notForest

-- the gated commute on a concrete reachable slack-fresh forest state
#assert_no_axioms FX1Poly.Polygraph.arcSlackForestState
#print axioms FX1Poly.Polygraph.arcSlackForestState
#assert_no_axioms FX1Poly.Polygraph.arcSlackForestState_isFresh
#print axioms FX1Poly.Polygraph.arcSlackForestState_isFresh
#assert_no_axioms FX1Poly.Polygraph.arcSlackForestState_isForest
#print axioms FX1Poly.Polygraph.arcSlackForestState_isForest
#assert_no_axioms FX1Poly.Polygraph.arcSlackRedexState
#print axioms FX1Poly.Polygraph.arcSlackRedexState
#assert_no_axioms FX1Poly.Polygraph.arcSlackReductState
#print axioms FX1Poly.Polygraph.arcSlackReductState
#assert_no_axioms FX1Poly.Polygraph.arcSlackForestPartitionComponentsAgree
#print axioms FX1Poly.Polygraph.arcSlackForestPartitionComponentsAgree

-- the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcFreshnessInvariantProbed
#print axioms FX1Poly.Polygraph.fxMode_hasArcFreshnessInvariantProbed

end FX1PolyAudit
