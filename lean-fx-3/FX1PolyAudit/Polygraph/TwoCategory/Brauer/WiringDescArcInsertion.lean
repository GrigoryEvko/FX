import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcInsertion

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescArcInsertion — zero-axiom gate (BRAUER r34)

Per-declaration zero-axiom gate for the LOCAL per-cup arc-insertion leg fuel: the distance-to-slot lex pair and its
`Nat` embedding, the tie-break bound, the two lex→`Nat` combine lemmas, the leftmost-cup distance read-off in arbitrary
cupless-prefix context, the general PRIMARY (distance) descent of a distant cup-sink, the flagship reduction across the
exact chain the global measure was refuted on, the per-cell drops, the honesty markers, and the machine-checked
terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.countAtoms
#assert_no_axioms FX1Poly.Polygraph.atomsRightOfFirstCup
#assert_no_axioms FX1Poly.Polygraph.straddleBitAtFirstCup
#assert_no_axioms FX1Poly.Polygraph.legLexFuel
#assert_no_axioms FX1Poly.Polygraph.straddleWindowBit_le_one
#assert_no_axioms FX1Poly.Polygraph.straddleBitAtFirstCup_le_one
#assert_no_axioms FX1Poly.Polygraph.legLex_lt_of_primary
#assert_no_axioms FX1Poly.Polygraph.legLex_lt_of_secondary
#assert_no_axioms FX1Poly.Polygraph.hasNoCup
#assert_no_axioms FX1Poly.Polygraph.atomsRightOfFirstCup_prefixCupless
#assert_no_axioms FX1Poly.Polygraph.atomsRightOfFirstCup_prefixCupless_nonCupThenCup
#assert_no_axioms FX1Poly.Polygraph.legFuel_leftmostCupCrossing_lt
#assert_no_axioms FX1Poly.Polygraph.legFuel_leftmostCupCap_lt
#assert_no_axioms FX1Poly.Polygraph.legFuelFold_throughReexposure_demo
#assert_no_axioms FX1Poly.Polygraph.legFuel_perCell_drops
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasLocalLegFuelDescent
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasLocalLegFuelGlobalFold
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_localLegFuelTerminalState

end FX1PolyAudit
