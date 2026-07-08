import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescJoinEvents

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescJoinEvents — zero-axiom gate (KEYSTONE3)

Per-declaration zero-axiom gate for the generic `stepWiring` engine's join-event reification: the union-find
no-op bridge, the decoded arc trace, the arc-fold link / loop reifications, and the one-step `stepWiring`
corollaries, plus the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the union-find no-op bridge
#assert_no_axioms FX1Poly.Polygraph.unionFindJoin_of_isSameComponent

-- the arc-fold link / loop reifications
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_fst_eq_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_snd_eq_countJoinEventLoops

-- the one-step stepWiring corollaries
#assert_no_axioms FX1Poly.Polygraph.stepWiring_links_eq_applyJoinEvents
#assert_no_axioms FX1Poly.Polygraph.stepWiring_loops_eq

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasWiringDescJoinEventReification

end FX1PolyAudit
