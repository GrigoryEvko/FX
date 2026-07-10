import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcAnchor

/-! # BRAUER-ARC-DESCENT r2 B5 — the terminal LEDGER (#2013 stays OPEN; the arc ends at the anchored-target wall)

THE FINAL ARC ROUND (complete-or-wall; no r3).  The r1 arc-descent measure pinned the pass-5-arc wall to the
adjacent-straddle cup slide and named the r2 residual as an ANCHORED `legDistance` off a fixed standard-form target.
r2 REFUTES that plan and records the honest permanent wall, machine-checked.

## The verdict, machine-checked

  * **B1 SHIPPED** (`fxBrauer_hasStandardFormReadbackFunction = true`): the standard-form readback
    `standardFormOfDiagram : DiagramType → Option BrauerStandardForm` ships — SOUND by construction
    (`standardFormOfDiagram_sound`), roundtripping on the planar-empty-middle reachable class, and EXHIBITING both
    walls by its `none`s (WALL-1 straddle non-planar, WALL-2 middle-permutation not inverted).
  * **B2 WALLED — the anchored measure cannot be built** (`fxBrauer_hasAnchoredMeasureTargetWall = true`):
    `anchoredMeasure_targetWall` proves the straddle target diagram `{ bottomCount := 1, topCount := 3,
    partner := [2, 3, 0, 1], loops := 0 }` is CROSSING (`straddleDiagram_isCrossing`), so no tail-cup-block standard
    form realizes it (the sound readback returns `none`), and r1's list-order resister still ascends.  This SHARPENS
    r1's `straddle_resists_arcMeasure` from "measure ascends" to "target does not exist".
  * **B3 / B4 DO NOT LAND** — the full fold and the V2 word-problem decision are NOT built:
    `fxBrauer_hasArcDescentFold`, `fxBrauer_hasBrauerV2FullCompleteness`, and `fxBrauer_hasBrauerCompleteness` STAY
    `false`.  NO flip is fabricated.
  * the crossing-block leg is already UNCONDITIONAL (`fxBrauer_hasCrossingOnlyCompletenessUnconditional = true`,
    `crossingCompleteness_inRange`, backed by the proven in-range readback) — the S_n middle block of Route B closes;
    the arc block (Route B's boundary permutations + planar TL core) does not.

## The three permanent WALL statements (the honest terminal, no r3)

  * **WALL-1 — the tail-cup-block NF is incomplete (MACHINE-CHECKED).**  There exist diagram-equal words whose
    diagram has a CROSSING boundary matching: `straddleDiagram_isCrossing` (`¬ IsNonCrossing 1 [2, 3, 0, 1]`) with
    `straddleDiagram = brauerDiagramOf 1 [cupAt 0, crossingAt 1]` (`straddleDiagram_eq`).  No `capWord ++ crossingWord
    ++ cupWord` over one bottom wire realizes it (the cup leg is essentially braided past the strand), so
    `standardFormOfDiagram` is PROVABLY partial (`standardFormOfDiagram_straddle_none`) and the anchored
    legDistance-to-tail-block is UNDEFINED on the straddle.

  * **WALL-2 — the readback-in-context gap.**  Even for planar-reachable diagrams, reading the middle permutation off
    requires the crossing-only readback lifted through a cap prefix + cup suffix; the proven readback
    (`brauerCrossingOnlyReadbackInRange_proof`) is standalone-from-`brauerSeed` only.
    `standardFormOfDiagram_pureCrossing_none` exhibits the gap: the planar-reachable pure-crossing diagram `[3,2,1,0]`
    reads back to `none` because the empty-middle reconstruction does not invert the through-strand permutation.

  * **WALL-3 — the free-vs-admission gap is the whole residual.**  `BrauerConv` is decided/complete zero-axiom
    (`decidableBrauerConv`, `brauerConv_complete`); the genuine #2013 residual is `BrauerConvFree8` completeness
    `brauerWords_equalMatching_conv` = deriving the connectivity-view move from the generating relations.  With the
    anchored tail-block route walled (WALL-1), the surviving route is S_n ⋉ TL (Route B): two boundary permutations
    sandwiching a planar TL core, whose crossing legs are unconditional (`crossingCompleteness_inRange`) but whose
    boundary-crossing read-off is exactly WALL-2.

Every wall is a ROUTE gap, not a truth gap — Lehrer–Zhang (arXiv:1207.5889, Thm 2.6) guarantees the seven/eight
relations are complete, so `brauerWords_equalMatching_conv` is TRUE.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★ **The BRAUER-ARC-DESCENT r2 terminal state — MACHINE-CHECKED.**  The readback FUNCTION and the anchored-target
WALL ship (B1 / B2); the full fold, the V2 completeness, and the master completeness stay `false` — #2013 does not
close on the anchored route, and the arc ends (no r3).  A `rfl`-conjunction the kernel checks over the shipped
markers. -/
theorem fxBrauer_arcAnchorTerminalState :
    fxBrauer_hasStandardFormReadbackFunction = true
      ∧ fxBrauer_hasAnchoredMeasureTargetWall = true
      ∧ fxBrauer_hasCrossingOnlyCompletenessUnconditional = true
      ∧ fxBrauer_hasArcDescentFold = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **The three permanent WALL statements, bundled and machine-checked.**  WALL-1: the straddle target is
non-planar (`straddleDiagram_isCrossing`) and its readback is `none` (no tail-block realizer).  WALL-2: the
planar-reachable pure-crossing diagram reads back to `none` (the middle permutation is not inverted).  Plus the
r1 resister (`straddle_resists_arcMeasure`) — the straddle is a genuine `BrauerConvFree8` move (`straddle_isMove`) on
which every list-order measure freezes-or-ascends. -/
theorem fxBrauer_arcAnchorWalls :
    (¬ IsNonCrossing straddleDiagram.bottomCount straddleDiagram.partner
        ∧ standardFormOfDiagram straddleDiagram = none)
      ∧ standardFormOfDiagram { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 } = none
      ∧ BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0]
      ∧ cupPositionSum [cupAt 0, crossingAt 1] < cupPositionSum [cupAt 1, crossingAt 0] :=
  ⟨⟨straddleDiagram_isCrossing, standardFormOfDiagram_straddle_none⟩,
   standardFormOfDiagram_pureCrossing_none, straddle_isMove, straddle_resists_arcMeasure.2⟩

/-- **Honesty marker — the BRAUER-ARC-DESCENT r2 ledger is RECORDED; #2013 stays OPEN, the arc ENDS.**  B1 (the
readback function) and B2 (the anchored-target wall) ship zero-axiom; the recon's anchored legDistance-to-tail-block
plan is REFUTED (the straddle target is non-planar, `fxBrauer_arcAnchorWalls`), so the full fold to Graham–Lehrer
standard form cannot be assembled on that route.  The genuine #2013 residual is `BrauerConvFree8` completeness via the
S_n ⋉ TL boundary-crossing route (WALL-3), whose crossing legs are unconditional
(`fxBrauer_hasCrossingOnlyCompletenessUnconditional`) but whose boundary read-off is the unbuilt readback-in-context
(WALL-2).  `fxBrauer_hasBrauerCompleteness` / `fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasArcDescentFold`
stay `false` — no flip fabricated.  This is the final arc round (no r3).  `= true`. -/
def fxBrauer_hasArcAnchorLedger : Bool := true

end FX1Poly.Polygraph
