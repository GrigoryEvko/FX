import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadback

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadback — zero-axiom gate (BREACH r4 P1: T2)

Per-declaration zero-axiom gate for the crossing-only readback STATE INVARIANT (T2): the boundary-view / permutation
-graph datatype, the seed, the one-step advance (the fresh-forest keystone), and the in-range fold.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- The permutation-graph boundary datatype
#assert_no_axioms FX1Poly.Polygraph.boundaryNodeAt
#assert_no_axioms FX1Poly.Polygraph.boundaryStrand
#assert_no_axioms FX1Poly.Polygraph.shuffleIndex
#assert_no_axioms FX1Poly.Polygraph.StateIsPermGraph

-- The T2 state invariant: seed + step (the fresh-forest keystone) + in-range fold
#assert_no_axioms FX1Poly.Polygraph.stateIsPermGraph_seed
#assert_no_axioms FX1Poly.Polygraph.stateIsPermGraph_step
#assert_no_axioms FX1Poly.Polygraph.stateIsPermGraph_ofInRange
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingReadbackStateInvariant

end FX1PolyAudit
