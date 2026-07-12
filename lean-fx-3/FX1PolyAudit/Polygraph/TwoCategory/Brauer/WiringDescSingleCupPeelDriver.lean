import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupPeelDriver

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescSingleCupPeelDriver — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r38 single-cup PEEL DRIVER: the unified three-fated outcome
(`SingleCupOutcome`), the OUTER sink-step combinator (`SingleCupOutcome.prepend`), the three terminal builders
(`outcomeArrivedOfDistantTail` / `outcomeAnnihilateS1` / `_S2` / `outcomeLoopAtZero`), the two named prepend seam steps
(`prependUntwist` / `prependStraddle`), the genuine outer structural recursion (`peelUntwistRun`), the four hostiles run
end-to-end (`peelHostileSnakeFirst` / `peelHostileUntwistDistant` / `peelHostileLoop` / `peelUntwistRunThenDistant_demo`)
with the honest raw-arrival false-negative companion (`peelHostileStraddleTail_rawArrivalFalseNegative`), the fate
read-off (`SingleCupOutcome.fate` / `peelHostile_fates`), the honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the indexed `SingleCupOutcome`
match in `prepend` and the `Nat`-structural `peelUntwistRun` recursion are both axiom-free (`List.length_append` and the
stdlib `Nat.beq_refl` LEAK `propext` and are deliberately avoided in the imported source).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SingleCupOutcome.prepend
#assert_no_axioms FX1Poly.Polygraph.outcomeArrivedOfDistantTail
#assert_no_axioms FX1Poly.Polygraph.outcomeAnnihilateS1
#assert_no_axioms FX1Poly.Polygraph.outcomeAnnihilateS2
#assert_no_axioms FX1Poly.Polygraph.outcomeLoopAtZero
#assert_no_axioms FX1Poly.Polygraph.prependUntwist
#assert_no_axioms FX1Poly.Polygraph.prependStraddle
#assert_no_axioms FX1Poly.Polygraph.peelUntwistRun
#assert_no_axioms FX1Poly.Polygraph.peelHostileSnakeFirst
#assert_no_axioms FX1Poly.Polygraph.peelHostileUntwistDistant
#assert_no_axioms FX1Poly.Polygraph.peelHostileLoop
#assert_no_axioms FX1Poly.Polygraph.peelUntwistRunThenDistant_demo
#assert_no_axioms FX1Poly.Polygraph.peelHostileStraddleTail_rawArrivalFalseNegative
#assert_no_axioms FX1Poly.Polygraph.SingleCupOutcome.fate
#assert_no_axioms FX1Poly.Polygraph.peelHostile_fates
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSingleCupOutcomeDriver
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSingleCupTotalDecision
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_singleCupPeelDriverTerminalState

-- Independent cross-check (mandatory, per the AuditAll zero-axiom protocol): the headline declarations print no axioms.
#print axioms FX1Poly.Polygraph.SingleCupOutcome.prepend
#print axioms FX1Poly.Polygraph.peelUntwistRun
#print axioms FX1Poly.Polygraph.peelHostile_fates
#print axioms FX1Poly.Polygraph.fxBrauer_singleCupPeelDriverTerminalState

end FX1PolyAudit
