import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCuplessPrefixStripDriver

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCuplessPrefixStripDriver — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r46 cupless-prefix STRIP driver: the single-atom cupless witness, the
three-fated prefix whisker + its fate-preservation check, the strip-augmented recursive driver + its flat surface, the
deep-tail discharge fires + fates, the census subsumption, the loop-behind-prefix honest wall, the totality refutation
(the exact unmet flip criterion + counterexample), the out-of-scope guard, the honesty markers, and the machine-checked
terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the single-atom cupless witness
is a structural `cond` reduction (`rw` + `rfl`, no propext), the whisker re-uses the shipped explicit-motive r42
`prependCuplessPrefix*` combinators, the driver is fuel-STRUCTURAL (no `WellFounded.fix` / `termination_by`), and the
single-atom peel reindexes by the DEFINITIONAL `[atom] ++ rest = atom :: rest` (no `Eq.rec`).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.hasNoCup_singleton_of_not_cup
#assert_no_axioms FX1Poly.Polygraph.whiskerNonLoopOutcome
#assert_no_axioms FX1Poly.Polygraph.whiskerNonLoopOutcomePreservesFate
#assert_no_axioms FX1Poly.Polygraph.driveRegionStripped
#assert_no_axioms FX1Poly.Polygraph.flatRegionDriveStripped
#assert_no_axioms FX1Poly.Polygraph.driveStrippedFiresOnDeepTail
#assert_no_axioms FX1Poly.Polygraph.driveStrippedFates
#assert_no_axioms FX1Poly.Polygraph.driveStrippedSubsumesCensus
#assert_no_axioms FX1Poly.Polygraph.driveStrippedLoopBehindPrefixStaysNone
#assert_no_axioms FX1Poly.Polygraph.driveStrippedTotalityRefutedByLoopBehindPrefix
#assert_no_axioms FX1Poly.Polygraph.driveStrippedOutOfScopeStaysNone
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCuplessPrefixStripArrivedAnnihilated
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCuplessPrefixLoopWhisker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_cuplessPrefixStripDriverTerminalState

end FX1PolyAudit
