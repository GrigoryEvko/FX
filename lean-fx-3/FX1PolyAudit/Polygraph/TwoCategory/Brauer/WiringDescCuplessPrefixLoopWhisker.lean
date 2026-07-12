import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCuplessPrefixLoopWhisker

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCuplessPrefixLoopWhisker — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r47 loop-behind-prefix whisker: the generic loop non-emptiness from a
positive global loop count, the state-threading interface reduction + fold-monotonicity dominance, the loop-behind-prefix
provider + its concrete demo / fate, the reflexive loop-bubble provider, the loop-stripped driver, the loop-behind-prefix
fires + fates, the census subsumption, the loops=0 four-class residue wall, the out-of-scope guard, the totality
refutation, the two honesty markers, and the machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the non-emptiness is the shipped
`Nat.not_succ_le_zero` path, the threading is `processBrauer_append` + `processFoldLoopsNonDecreasing` (structural), the
provider uses the reflexive `BrauerConvFree8` (no opaque transport), and the driver is a STRUCTURAL top-level match +
`Nat.beq` enum + `Nat.decLe` dependent-if over the shipped fuel driver (no `WellFounded.fix` / `termination_by`).  The
concrete loop counts are `decide` over `Nat.decLe` (structural).  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.loopsPositiveNotEmpty
#assert_no_axioms FX1Poly.Polygraph.loopBehindPrefixLoopsThreaded
#assert_no_axioms FX1Poly.Polygraph.loopBehindPrefixLoopsGeAfterCupCap
#assert_no_axioms FX1Poly.Polygraph.prependCuplessPrefixLoop
#assert_no_axioms FX1Poly.Polygraph.loopBehindPrefixDemo
#assert_no_axioms FX1Poly.Polygraph.loopBehindPrefixDemo_fate
#assert_no_axioms FX1Poly.Polygraph.outcomeReflexiveLoop
#assert_no_axioms FX1Poly.Polygraph.flatRegionDriveLoopStripped
#assert_no_axioms FX1Poly.Polygraph.driveLoopStrippedFiresOnLoopBehindPrefix
#assert_no_axioms FX1Poly.Polygraph.driveLoopStrippedFates
#assert_no_axioms FX1Poly.Polygraph.driveLoopStrippedSubsumesCensus
#assert_no_axioms FX1Poly.Polygraph.driveLoopStrippedZeroLoopResidueStaysNone
#assert_no_axioms FX1Poly.Polygraph.driveLoopStrippedOutOfScopeStaysNone
#assert_no_axioms FX1Poly.Polygraph.driveLoopStrippedTotalityStillRefuted
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCuplessPrefixLoopWhiskerBuilt
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSingleCupZeroLoopSettling
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_cuplessPrefixLoopWhiskerTerminalState

end FX1PolyAudit
