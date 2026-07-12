import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorArms

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorArms — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r44 deferred flat→descriptor ARMS: the two SNAKE arms extending the r43
`extractCupHead` on its `none` branch (`extractCupHeadWithSnakes` / `extractWorkingRegionWithSnakes` /
`flatRegionDispatchWithSnakes`), the coverage upgrade of the two snake clauses to `isSome`, the dispatch firing on the
snakes, the honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the snake roundtrips are
`Nat.eq_of_beq_eq_true` + `capAt_of_wiring` (structure eta off the `DecidableEq WiringDesc` equality, no
`List.append_assoc`, no `Nat.beq_refl`), and the transport is the r41 shipped explicit-motive `Eq.rec`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.extractCupHeadWithSnakes
#assert_no_axioms FX1Poly.Polygraph.extractWorkingRegionWithSnakes
#assert_no_axioms FX1Poly.Polygraph.flatRegionDispatchWithSnakes
#assert_no_axioms FX1Poly.Polygraph.extractWorkingRegionWithSnakes_coverage
#assert_no_axioms FX1Poly.Polygraph.flatDispatchWithSnakes_firesOnSnakes
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFlatSnakeArms
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasFlatSnakeSynthesisGap
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_flatSnakeArmsTerminalState

end FX1PolyAudit
