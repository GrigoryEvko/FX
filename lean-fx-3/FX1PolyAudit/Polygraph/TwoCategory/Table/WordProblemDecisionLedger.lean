import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.WordProblemDecisionLedger

/-! # FX1PolyAudit/.../WordProblemDecisionLedger — zero-axiom gate

Per-declaration zero-axiom gate for the grand word-problem DECISION ledger core (WP-LEDGER #2048): the
decided-9 walker enumeration, the per-rung decision-status map, the coverage counts, the unique-gap theorem
(cyclic-3 is the sole rung with no shipped decider), and the honest markers.

Structural recursion over the walker enum with `List.Mem` constructors + `noConfusion` clashes; must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `decide`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemDecidedWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemDecidedWalkerCountIsNine
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemDecidedWalkersExhaustive
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemDecisionStatus
#assert_no_axioms FX1Poly.Polygraph.Table.hasShippedWordProblemDecider
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemDecidedWalkersWithShippedDecider
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemShippedDeciderCountIsNine
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemFullTwoCellDecidedWalkers
#assert_no_axioms FX1Poly.Polygraph.Table.wordProblemFullTwoCellDeciderCountIsSix
#assert_no_axioms FX1Poly.Polygraph.Table.allWordProblemDecidedWalkersHaveShippedDecider
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpLedger_decisionCoverageNineOfNine
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpLedger_cyclicThreeDecisionShipped
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpLedger_adjunctionPresentationWalledDecisionDecided
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpLedger_uniformInterfaceCoversFourOfSix
#assert_no_axioms FX1Poly.Polygraph.Table.fxWpLedger_grandLedgerClosed

end FX1PolyAudit
