import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescGeneratorBridge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescGeneratorBridge — zero-axiom gate (BRAUER-MIDDLE r10 B1)

Per-declaration zero-axiom gate for the two generator bridges routing `stepWiring` at `cupWiring` / `capWiring`
to the shipped `stepCup` / `stepCap`: the two structural plumbing lemmas (`removeTwoAt_succ_cons`,
`natListRemoveManyAt_two_eq_removeTwoAt`, `natListInsertAt_nil`), the three arc-fold reductions
(`stepWiringArcs_cup_eq`, `stepWiringArcs_cap_eq_same`, `stepWiringArcs_cap_eq_diff`), the two bridges
(`stepWiring_capWiring_eq_stepCap`, `stepWiring_cupWiring_eq_stepCup`), and the honesty marker.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- the two structural plumbing lemmas
#assert_no_axioms FX1Poly.Polygraph.removeTwoAt_succ_cons
#assert_no_axioms FX1Poly.Polygraph.natListRemoveManyAt_two_eq_removeTwoAt
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_nil

-- the three arc-fold reductions
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_cup_eq
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_cap_eq_same
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_cap_eq_diff

-- the two generator bridges
#assert_no_axioms FX1Poly.Polygraph.stepWiring_capWiring_eq_stepCap
#assert_no_axioms FX1Poly.Polygraph.stepWiring_cupWiring_eq_stepCup

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasGeneratorBridge

end FX1PolyAudit
