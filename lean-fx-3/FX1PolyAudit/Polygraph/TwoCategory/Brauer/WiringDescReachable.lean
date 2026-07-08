import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReachable

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescReachable — zero-axiom gate (KEYSTONE6 brick A)

Per-declaration zero-axiom gate for the reachable-state invariant + the refutation of the literal
`WiringDescDisjointWindowFresh`: the block-removal membership / bound (`mem_natListRemoveManyAt`,
`natListRemoveManyAt_all_lt`), the endpoint-node bound (`wiringEndpointNode_lt`), the arc-fold bound
(`stepWiringArcs_all_lt`), the fresh-preservation step (`wiringDescStateFresh_stepWiring`), the four-invariant fold
(`brauerStateConditions_stepBrauerAtom` / `_processBrauer`, `brauerStateConditions_seed`,
`brauerReachable_conditions`), the reachable interchange (`brauer_reachable_interchange`), the fresh adversary
(`outOfRangeFreshState_fresh`), the literal refutation (`wiringDescDisjointWindowFresh_false`), and the honesty
markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- block-removal membership + bound, endpoint-node bound, arc-fold bound
#assert_no_axioms FX1Poly.Polygraph.mem_natListRemoveManyAt
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt_all_lt
#assert_no_axioms FX1Poly.Polygraph.wiringEndpointNode_lt
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_all_lt

-- one-step fresh preservation
#assert_no_axioms FX1Poly.Polygraph.wiringDescStateFresh_stepWiring

-- the four-invariant reachable-state fold
#assert_no_axioms FX1Poly.Polygraph.brauerStateConditions_stepBrauerAtom
#assert_no_axioms FX1Poly.Polygraph.brauerStateConditions_processBrauer
#assert_no_axioms FX1Poly.Polygraph.brauerStateConditions_seed
#assert_no_axioms FX1Poly.Polygraph.brauerReachable_conditions

-- the reachable-state interchange
#assert_no_axioms FX1Poly.Polygraph.brauer_reachable_interchange

-- the literal refutation
#assert_no_axioms FX1Poly.Polygraph.outOfRangeFreshState_fresh
#assert_no_axioms FX1Poly.Polygraph.wiringDescDisjointWindowFresh_false

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescStateFreshStep
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasReachableStateInvariant
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescDisjointWindowFreshRefuted

end FX1PolyAudit
