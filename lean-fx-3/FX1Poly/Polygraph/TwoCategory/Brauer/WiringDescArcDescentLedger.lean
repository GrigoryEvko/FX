import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcDescentFold
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingComplete

/-! # BRAUER-ARC-DESCENT r1 B4 — the ledger (#2013 does NOT close; the wall is pinned to the straddle-reposition)

The bequest (`Brauer/WiringDescCrossingComplete.lean:40-42`) was a distinguished-arc lexicographic descent
`(outermostUnsortedArc, arcSpan, legDistance)` to breach the pass-5-arc wall.  This round SHARPENS the wall to a
single move and ships the descending fragment machine-checked; it does NOT close #2013.

## The verdict, machine-checked

  * **B1 SHIPPED** (`fxBrauer_hasArcDescentMeasure = true`): the list-order lex measure
    `(cupNonCupInversions, cupPositionSum)` and its `Nat` embedding `arcMeasure` STRICTLY DESCEND on the three
    disjoint-support / cup-cup shipped cup-sink slides — including the crux cup-past-cap commute the frozen
    `inversionCount` could not descend (`cupCap_inversions_lt`).  Non-vacuity on the recon's minimal interleaved
    instance: fuel `8 → 0`.
  * **B2 SHIPPED (partial)** (`fxBrauer_hasArcDescentSinkMechanism = true`): the Σ-carried `recCombConv`-shaped
    sink fold mechanism — the three rungs thread a `BrauerConvFree8` accumulator across a slide AND certify a strict
    `arcMeasure` fuel drop; `arcSinkFold_demo` composes two rungs (fuel `16 → 8 → 0`).
  * **B2 FULL FOLD WALLS** (`fxBrauer_hasArcDescentFold = false`) and **B3 does NOT land** — the assembly
    `brauerWords_equalMatching_conv` and the decision are NOT built, so
    `fxBrauer_hasBrauerV2FullCompleteness = false` and #2013 stays open.

## The EXACT resisting move + configuration (the adjusted-measure attempt log)

The recon's table attributed the interleaved-case descent to `cupSlideStraddleFree8_inContext`, but that lemma is
the ADJACENT-STRADDLE cup-past-crossing row `cupSlideRelation` `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]`,
NOT the cup-past-cap distant slide.  The recon's legDistance-to-a-fixed-slot idea was concretized as the fully
syntactic "list-order distance to the tail block" = `cupNonCupInversions`, with `cupPositionSum` as the
sibling-cup secondary.  Attempt log against that adjusted measure:

  * distant cup-past-cap  `[cupAt p, capAt (q+2)] ↝ [capAt q, cupAt p]`   — primary `−1`  ⟹ DESCENDS.
  * distant cup-past-cross `[cupAt a, crossingAt (c+2)] ↝ [crossingAt c, cupAt a]` — primary `−1` ⟹ DESCENDS.
  * cup-past-cup `[cupAt L, cupAt (R+2)] ↝ [cupAt R, cupAt L]`  — primary held, secondary `−2` ⟹ DESCENDS.
  * **adjacent straddle `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]`  — primary FROZEN (`1 = 1`),
    secondary ASCENDS (`0 < 1`)  ⟹ RESISTS** (`straddle_resists_arcMeasure`).

The straddle keeps the cup FIRST in list order (no list-order sink) while braiding its leg — a pure BOUNDARY
reposition.  Every list-order syntactic measure is therefore frozen-or-ascending on it: the resistance is
structural, not an artifact of this particular pair of coordinates.  Its descent genuinely needs the boundary-slot
`legDistance`, which is read off `standardForm(DiagramType)` — the crossing-only readback residual.

## The 2-round cap — the ONE precise surviving node for r2

Per the bequest the arc gets a 2-round cap.  r2 (if taken) attacks EXACTLY ONE node: the crossing-only readback
`DiagramType → BrauerStandardForm` (`fxBrauer_hasCrossingOnlyReadback`, `Brauer/WiringDescBrauerLedger.lean`,
currently `false`).  It supplies the FIXED boundary target slot the straddle's `legDistance` measures to; with that
slot, `legDistance` becomes a genuine boundary monovariant (the straddle's cup leg moves one boundary-slot closer to
a fixed target it can never reach twice), replacing `cupPositionSum` as the secondary and covering the straddle.
Without the readback there is NO list-order fallback — this is the permanent wall statement for the syntactic route.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★ **The BRAUER-ARC-DESCENT r1 terminal state — MACHINE-CHECKED.**  The descent MEASURE and the Σ-carried sink
fold MECHANISM ship (B1 / B2-partial); the FULL fold and the V2 completeness stay `false` — #2013 does not close on
the syntactic route.  A `rfl`-conjunction the kernel checks over the shipped markers. -/
theorem fxBrauer_arcDescentTerminalState :
    fxBrauer_hasArcDescentMeasure = true
      ∧ fxBrauer_hasArcDescentSinkMechanism = true
      ∧ fxBrauer_hasArcDescentFullMonovariant = false
      ∧ fxBrauer_hasArcDescentFold = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **The pinned wall — the resister is EXACTLY the adjacent-straddle cup slide, proven.**  The descent covers
the three disjoint-support / cup-cup slides (the crux cup-past-cap included) but the straddle `cupSlideRelation`
freezes the primary and ascends the secondary — bundled as the honest wall.  The straddle IS a genuine
`BrauerConvFree8` move (`straddle_isMove`), so the resistance is real, not vacuous. -/
theorem fxBrauer_arcDescentWall :
    (cupNonCupInversions [cupAt 1, crossingAt 0] = cupNonCupInversions [cupAt 0, crossingAt 1]
        ∧ cupPositionSum [cupAt 0, crossingAt 1] < cupPositionSum [cupAt 1, crossingAt 0])
      ∧ BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0]
      ∧ cupNonCupInversions [capAt 0, cupAt 0] < cupNonCupInversions [cupAt 0, capAt 2] :=
  ⟨straddle_resists_arcMeasure, straddle_isMove, arcDescent_nonVacuity_cupCap.2.1⟩

/-- **Honesty marker — the BRAUER-ARC-DESCENT r1 ledger is RECORDED; #2013 stays OPEN.**  B1 (the descent measure)
and B2-partial (the Σ-carried sink mechanism) ship zero-axiom; the full fold to Graham–Lehrer standard form WALLS at
the adjacent-straddle cup slide (`fxBrauer_arcDescentWall`), which every list-order measure freezes-or-ascends on.
The r2 target is exactly ONE node: the crossing-only readback `DiagramType → BrauerStandardForm`
(`fxBrauer_hasCrossingOnlyReadback`), supplying the fixed boundary slot the straddle's `legDistance` needs.
`fxBrauer_hasBrauerV2FullCompleteness` stays `false`.  `= true`. -/
def fxBrauer_hasArcDescentLedger : Bool := true

end FX1Poly.Polygraph
