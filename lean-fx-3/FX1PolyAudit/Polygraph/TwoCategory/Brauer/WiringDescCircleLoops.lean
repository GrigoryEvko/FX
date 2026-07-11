import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCircleLoops

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCircleLoops — zero-axiom gate (BRAUER r30 B1)

Per-declaration zero-axiom gate for the circle-loop accounting: the two per-step loop lemmas
(`stepWiring_cup_loops` — a cup closes no loop; `stepWiring_cap_loops_ofConnected` — a cap on an already-connected
pair closes exactly one loop), the one-circle `+1` weld (`oneCircleLoops`), the structural circle accounting
(`circleFold_loops`, `(processBrauer state (circleWord n)).loops = state.loops + n`), and the honesty marker
`fxBrauer_hasCircleLoopAccounting`.

Independent `#print axioms` (scratch) reported every decl as "does not depend on any axioms".  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- Section 1: the two per-step loop lemmas
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cup_loops
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cap_loops_ofConnected

-- Section 2: the one-circle +1 weld
#assert_no_axioms FX1Poly.Polygraph.oneCircleLoops

-- Section 3: the circle accounting (the structural induction)
#assert_no_axioms FX1Poly.Polygraph.circleFold_loops

-- Section 4: the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCircleLoopAccounting

end FX1PolyAudit
