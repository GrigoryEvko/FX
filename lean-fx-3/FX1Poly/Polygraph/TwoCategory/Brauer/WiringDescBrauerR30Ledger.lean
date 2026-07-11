import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCircleLoops
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescOpenEndsDistinct
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingDistinct
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerR29Ledger

/-! # BRAUER r30 — THE GRAND LEDGER: leg 1 (circle) CLOSED, leg 2 (zero-loops) invariant + preservation CLOSED

The r29 loops wall named the SOLE residual of T-CLOSE(b): the loops field `F.loops = d.loops`, split into TWO legs —
a circle-loop accounting and a boundary-word-adds-0-loops leg (needing a fresh connectivity invariant).  r30 grinds
both legs to their honest floor.

## Shipped (true) — the r30 delta

  * **Leg 1 — THE CIRCLE ACCOUNTING (B1, CLOSED).**  `fxBrauer_hasCircleLoopAccounting`: `circleFold_loops` proves,
    zero-axiom and structural, `(processBrauer state (circleWord n)).loops = state.loops + n` for every fresh forest
    state — the exact loop-tracking mirror of the shipped `circleFold_openWires`.  The one-circle `+1` weld
    (`oneCircleLoops`) rests on `stepWiring_cup_loops` (a cup closes no loop, by fresh distinctness) and
    `stepWiring_cap_loops_ofConnected` (a cap on an already-connected pair closes exactly one loop).  Eval-probed
    (`circleWord 3 ↦ 3`, `5 ↦ 5`, `4 + 3 = 7`) before the induction.

  * **Leg 2 — THE ZERO-LOOPS INVARIANT + its FULL preservation (B2, cap side + crossing).**  The invariant
    `BrauerOpenEndsDistinct` (the FC-3 port to the generic `WireState`/`stepWiring` engine) holds at the seed
    (`brauerOpenEndsDistinct_seed`, S) and is PRESERVED by both a cap (`brauerOpenEndsDistinct_stepWiringCap`, C2 —
    `fxBrauer_hasOpenEndsDistinctCapSide`) and a crossing (`brauerOpenEndsDistinct_stepWiringCrossing`, X —
    `fxBrauer_hasOpenEndsDistinctCrossing`, the heaviest new lemma, the pullback along the window transposition
    `crossingJoin_transposition_view`).  A cap on a distinct pair closes NO loop (`stepWiring_cap_loops_ofDistinct`,
    C1) — the fold's caps never fire on a pre-connected pair.  Boundary-word-zero eval-probed `0`/`0` on
    adversarial-B / monster.

## The r30 residual — leg 2's loops-accounting ASSEMBLY (`fxBrauer_hasFoldLoopsCorrectness` STILL `false`)

The invariant and its per-step preservation are shipped; the boundary-word-zero `(processBrauer (brauerSeed bc)
boundaryWord).loops = 0` still needs (a) the crossing loops-zero re-export (a public clone of the readback-private
`stepWiring_crossing_loops`), and (b) the phase-fold assembly — `crossingWord_loops_zero` / `cupWord_loops_zero` (via
freshness) / `capWord_loops_zero_ofDistinct` (via C1+C2), chained through `standardFormFold_appendSplit` with the
in-range gate supplied by the shipped general `wellFormedBrauerFold_correctedWord_general`.  That assembly is the
named r31 residual; the loops field is NOT yet closed in general, so NO master flips.

## The masters (census carried, all `false`)

Since the loops field stays open, the four reconstruction masters that would flip WITH it stay `false`:
`fxBrauer_hasFoldAlignmentE3`, `fxBrauer_hasFoldTargetHonestAssembly`, `fxBrauer_hasTagCorrDisjoint`,
`fxBrauer_hasTagCorrExtraction`.  The three completeness masters are gated on a DIFFERENT, harder object —
`BrauerExt5CorrectedFoldReaches` (the Lehrer–Zhang straightening / the pass-5-arc interleaved-arc jam `i < k < j <
l`), NOT the loops field — so `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`, and
`fxBrauer_hasFreeBrauerStraighteningNF` stay `false` regardless.  #2013 does NOT close at r30.

Raw Lean 4 + Init.  A `rfl`-conjunction the kernel checks.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★★ **THE BRAUER r30 GRAND LEDGER — MACHINE-CHECKED.**  The r30 delta is `true`: leg 1 the circle accounting
(`fxBrauer_hasCircleLoopAccounting`) and leg 2 the zero-loops invariant with its FULL per-step preservation — cap side
(`fxBrauer_hasOpenEndsDistinctCapSide`) and crossing (`fxBrauer_hasOpenEndsDistinctCrossing`).  Every WALL is `false`:
the loops-field residual (`fxBrauer_hasFoldLoopsCorrectness`, now reduced to the phase-fold ASSEMBLY of leg 2 — its
invariant and per-step preservation are shipped), the four reconstruction masters (`fxBrauer_hasFoldAlignmentE3`,
`fxBrauer_hasFoldTargetHonestAssembly`, `fxBrauer_hasTagCorrDisjoint`, `fxBrauer_hasTagCorrExtraction`, which flip WITH
the loops field), and the three completeness masters (`fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness`, `fxBrauer_hasFreeBrauerStraighteningNF`, gated on the straightening
`BrauerExt5CorrectedFoldReaches`, not the loops field).  A `rfl`-conjunction: r30 closes leg 1 and leg 2's invariant +
preservation, but leg 2's loops-accounting assembly is unbuilt, so no master flips and #2013 does NOT close. -/
theorem fxBrauer_r30GrandLedger :
    (fxBrauer_hasCircleLoopAccounting = true)
    ∧ (fxBrauer_hasOpenEndsDistinctCapSide = true
      ∧ fxBrauer_hasOpenEndsDistinctCrossing = true)
    ∧ (fxBrauer_hasFoldLoopsCorrectness = false)
    ∧ (fxBrauer_hasFoldAlignmentE3 = false
      ∧ fxBrauer_hasFoldTargetHonestAssembly = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨rfl, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Honesty marker — #2013 (WP-BRAUER-4) is NOT complete after r30; leg 2's loops-accounting assembly is the sole
loops-field residual.**  r30 closed leg 1 (circle accounting) and leg 2's invariant + full per-step preservation
(seed / cap / crossing); the boundary-word-zero phase-fold assembly (`fxBrauer_hasFoldLoopsCorrectness = false`) is the
one honest wall between r30 and T-CLOSE(b), and the straightening (`BrauerExt5CorrectedFoldReaches`) remains the
separate wall on the completeness masters.  `= false`. -/
def fxBrauer_hasBrauerR30Complete : Bool := false

end FX1Poly.Polygraph
