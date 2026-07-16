import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.WordProblemDecisionWitnessBundle

/-! # FX1PolyAudit/.../WordProblemDecisionWitnessBundle — zero-axiom gate

Per-declaration zero-axiom gate for the grounded decider bundle (WP-LEDGER #2048).  Each `wpLedger*Decider`
is a definitional alias of a real word-problem decider, so `#assert_no_axioms` on the alias TRANSITIVELY
certifies the decider itself is axiom-free — machine-checking the ledger's claim that the decided-10's deciders
are zero-axiom, not merely that this wrapper is.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerInvolutionDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerCyclicThreeDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerMonadDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerIdempotentDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerComonadDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerIdempotentComonadDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerKZEqDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerKZOrderDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerCoKZOrderDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerAdjunctionDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wpLedgerOperadDecider
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpLedger_tenDecidersHeldAndGrounded

end FX1PolyAudit
