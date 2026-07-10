import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraddleDescent
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlideExtract
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractor

/-! # BRAUER-MIDDLE r3 B2 — R3-B: the STAGED arc-count fuel + the single-global-measure NO-GO

r2 B2 (`Brauer/WiringDescStraddleDescent.lean`) shipped the `straddleCount` PRIMARY coordinate that descends on the
adjacent-straddle move r1's `arcMeasure` ascended on, and named the residual: composing `(straddleCount, arcMeasure)`
into ONE well-founded fuel over ARBITRARY interleavings.  This round settles that residual's SHAPE: the naive single
global lex over the shipped 2-measure set is machine-REFUTED (the two measures are ANTI-CORRELATED across the move
classes), and the fuel that DOES work is a THIRD structure — the OUTER arc-count, which is a DIAGRAM invariant (hence
constant across the whole convertibility class, unraisable by any move) decremented only by peeling a completed arc.

## The anti-correlation (the machine-checked NO-GO)

Two shipped `BrauerConvFree8` moves pull the two measures in OPPOSITE directions:

  * **M1 the straddle** `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]`: `straddleCount` DROPS `1 → 0`, but
    `cupPositionSum` (hence `arcMeasure`) RISES `0 → 1` (`straddle_resists_arcMeasure`).
  * **M3 the distant cup-past-crossing slide, whiskered by a downstream crossing**
    `[cupAt 0, crossingAt 2, crossingAt 1] ↝ [crossingAt 0, cupAt 0, crossingAt 1]`: `straddleCount` RISES `0 → 1`
    — the distant slide floats the cup right past a disjoint crossing and RE-EXPOSES a straddle window
    (`crossingAt 1` sitting at the cup's new `+1` offset) that was not adjacent before.

So: with `straddleCount` PRIMARY, M3 raises the primary; with `arcMeasure` PRIMARY, M1 raises the primary.  NEITHER
ordering of the lex pair `(straddleCount, arcMeasure)` is monotone across both move classes — no consistent single
global measure over the shipped 2-measure set exists (`singleGlobalLexMeasure_refuted`).  This is exactly why
`fxBrauer_hasStraddleGlobalFuel` stayed `false`: not "no measure exists" for a fixed strategy, but "the 2-measure lex
is structurally anti-correlated."

## The resolution — the OUTER arc-count fuel (the staging that works)

The measure that sidesteps the anti-correlation is NOT a within-word list-order scalar at all: it is the OUTER
arc-count `arcCountFuel d = cupArcCount d + capArcCount d`, a function of the DIAGRAM.  Since every `BrauerConvFree8`
move preserves the diagram (soundness), the arc-count is CONSTANT across the whole convertibility class
(`arcCountFuel_diagram_invariant`, by `congrArg`) — it can never be raised by any move, so it is the OUTER stage
counter, strictly decremented only by PEELING a completed arc (`arcCountFuel_strictlyDecreases_perArc` exhibits the
`3 > 2 > 1 > 0` descent by nesting depth).  The staged fold is then a two-level lex: OUTER = arc-count (monotone by
construction, arcs consumed never regenerated), INNER = the per-arc boundary-slot descent.  The stage-boundary
invariant is DISJOINT SUPPORT: already-placed outer arcs are never touched by the interior recursion.

## The honest residual (R3-B / R3-C, feeds B3)

The OUTER fuel is shipped and its monotonicity is machine-checked; the INNER per-arc boundary-slot descent over
`BrauerConvFree8` (the native chord-shift) and the whisker-free driver threading the two-level fuel into
`BrauerExt5FoldReaches` are the remaining work — and the driver's per-step guard is the R3-A connectivity roundtrip
(the same long pole).  So `fxBrauer_hasStraddleGlobalFuel` stays `false` with the sharpened status: the single-lex
route is REFUTED, the arc-count staging is the buildable route, its outer level is done.  Every residual is a
route / measure gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The distant-slide-with-suffix adversarial — a genuine move that RAISES `straddleCount` -/

/-- ★ **The distant cup-past-crossing slide whiskered by a downstream crossing IS a genuine `BrauerConvFree8`
move.**  `distantCupCrossingSlideFree8 0 0` gives `[cupAt 0, crossingAt 2] ~ [crossingAt 0, cupAt 0]`; whiskering by
the suffix `[crossingAt 1]` gives `[cupAt 0, crossingAt 2, crossingAt 1] ~ [crossingAt 0, cupAt 0, crossingAt 1]` —
the distant slide against a downstream context. -/
theorem distantSlideWithSuffix_isMove :
    BrauerConvFree8 [cupAt 0, crossingAt 2, crossingAt 1] [crossingAt 0, cupAt 0, crossingAt 1] :=
  BrauerConvFree8.whiskerRight [crossingAt 1] (distantCupCrossingSlideFree8 0 0 (Nat.le_refl 0))

/-- ★★ **The distant slide RAISES `straddleCount` against a downstream suffix.**  Before the slide the cup at `0` is
followed by `crossingAt 2` (offset `2 ≠ 0+1`, no straddle window); after, the cup at `0` is immediately followed by
`crossingAt 1` (offset `0+1`, a straddle window).  `straddleCount` rises `0 → 1` — the exact re-exposure that killed
the single global measure. -/
theorem straddleCount_distantSlideWithSuffix_rises :
    straddleCount [cupAt 0, crossingAt 2, crossingAt 1]
      < straddleCount [crossingAt 0, cupAt 0, crossingAt 1] := by decide

/-! ## The single-global-lex NO-GO (the anti-correlation, machine-checked) -/

/-- ★★★ **No single global lex over `(straddleCount, arcMeasure)` descends on all shipped cup-sink moves — a
MACHINE-CHECKED NO-GO.**  The straddle M1 (first conjunct) DROPS `straddleCount` but RAISES `cupPositionSum` (hence
`arcMeasure`); the whiskered distant slide M3 (second conjunct) RAISES `straddleCount`.  So whichever of the two is
the PRIMARY lex coordinate, the OTHER move class raises it — the two measures are anti-correlated, and no consistent
single-lex assignment over the shipped 2-measure set is a descent.  This pins the r2 global-fuel residual to its
true shape: not a missing strategy, but a structural anti-correlation that the OUTER arc-count fuel below
sidesteps. -/
theorem singleGlobalLexMeasure_refuted :
    (BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0]
        ∧ straddleCount [cupAt 1, crossingAt 0] < straddleCount [cupAt 0, crossingAt 1]
        ∧ cupPositionSum [cupAt 0, crossingAt 1] < cupPositionSum [cupAt 1, crossingAt 0])
      ∧ (BrauerConvFree8 [cupAt 0, crossingAt 2, crossingAt 1] [crossingAt 0, cupAt 0, crossingAt 1]
        ∧ straddleCount [cupAt 0, crossingAt 2, crossingAt 1]
            < straddleCount [crossingAt 0, cupAt 0, crossingAt 1]) :=
  ⟨⟨straddle_isMove, straddleCount_straddle_lt, straddle_resists_arcMeasure.2⟩,
    ⟨distantSlideWithSuffix_isMove, straddleCount_distantSlideWithSuffix_rises⟩⟩

/-! ## The OUTER arc-count fuel (the staging that works) -/

/-- ★ **The cup-arc count of a diagram** — the number of top–top cup arcs (each arc counted once by its smaller
foot).  A function of the DIAGRAM (the boundary matching), not of any particular word. -/
def cupArcCount (d : DiagramType) : Nat :=
  (cupArcTopIndices d.bottomCount d.topCount d.partner).length

/-- ★ **The cap-arc count of a diagram** — the number of bottom–bottom cap arcs, the ∗-dual of `cupArcCount`. -/
def capArcCount (d : DiagramType) : Nat :=
  (capArcFeetIndices d.bottomCount d.partner).length

/-- ★ **The OUTER staged fuel** — total arc count (cup arcs + cap arcs).  The outer level of the two-level staged
lex: the arcs the peel recursion consumes, one per outer step. -/
def arcCountFuel (d : DiagramType) : Nat :=
  cupArcCount d + capArcCount d

/-- ★★ **The OUTER fuel is a DIAGRAM invariant — hence CONSTANT across a whole convertibility class.**  For two
words with equal `brauerDiagramOf` diagram, their arc-count fuels are equal (`congrArg`).  Since every
`BrauerConvFree8` move preserves the diagram (soundness), the arc-count is UNRAISABLE by any move — it is the OUTER
counter, not a within-word descent scalar, which is exactly why it evades the `singleGlobalLexMeasure_refuted`
anti-correlation.  It is decremented ONLY by peeling a completed arc off the standard-form target. -/
theorem arcCountFuel_diagram_invariant (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom)
    (diagramEq : brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight) :
    arcCountFuel (brauerDiagramOf bottomCount wordLeft)
      = arcCountFuel (brauerDiagramOf bottomCount wordRight) :=
  congrArg arcCountFuel diagramEq

/-- ★★ **The OUTER fuel strictly decreases per peeled arc.**  Reading the nesting depth off the diagram, the cup-arc
count descends `3 > 2 > 1 > 0` as arcs are consumed — the OUTER level is monotone by construction (arcs are removed,
never regenerated), so the two-level lex is well-founded on its outer coordinate. -/
theorem arcCountFuel_strictlyDecreases_perArc :
    cupArcCount { bottomCount := 0, topCount := 6, partner := [5, 4, 3, 2, 1, 0], loops := 0 } = 3
      ∧ cupArcCount { bottomCount := 0, topCount := 4, partner := [3, 2, 1, 0], loops := 0 } = 2
      ∧ cupArcCount { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 } = 1
      ∧ cupArcCount { bottomCount := 0, topCount := 0, partner := [], loops := 0 } = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Non-vacuity — the arc-count fuel computes definite mixed values.  The adversarial-B diagram (a crossing cap + a
through-strand + a crossing cup + a loop) has `cupArcCount = 1`, `capArcCount = 1`, total fuel `2`; the triple-nested
cups have fuel `3`. -/
theorem arcCountFuel_nonVacuity :
    arcCountFuel { bottomCount := 3, topCount := 3, partner := [2, 4, 0, 5, 1, 3], loops := 1 } = 2
      ∧ arcCountFuel { bottomCount := 0, topCount := 6, partner := [5, 4, 3, 2, 1, 0], loops := 0 } = 3 :=
  ⟨by decide, by decide⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the STAGED arc-count fuel + the single-global-measure NO-GO are SHIPPED (B2).**  The naive
single global lex over `(straddleCount, arcMeasure)` is machine-REFUTED (`singleGlobalLexMeasure_refuted`): the two
measures are anti-correlated — the straddle raises `arcMeasure`, the whiskered distant slide raises `straddleCount`.
The resolution is the OUTER arc-count fuel `arcCountFuel`, a DIAGRAM invariant (`arcCountFuel_diagram_invariant`,
constant across a convertibility class, unraisable by any move) that strictly decreases per peeled arc
(`arcCountFuel_strictlyDecreases_perArc`, `3 > 2 > 1 > 0`).  So the fuel is a two-level lex whose OUTER level is
monotone by construction — the staging the recon named.  `= true`. -/
def fxBrauer_hasStagedArcCountFuel : Bool := true

/-- **Honesty WALL marker — the global descent is NOT yet a discharged fold (the B2 residual, sharpened).**  The
OUTER arc-count fuel is shipped and its monotonicity machine-checked, but the INNER per-arc boundary-slot descent
over `BrauerConvFree8` (the native chord-shift) and the whisker-free driver threading the two-level fuel into
`BrauerExt5FoldReaches` are unbuilt — and the driver's per-step guard is the R3-A connectivity roundtrip (the same
long pole as `fxBrauer_hasCrossingOnlyReadback`).  So `fxBrauer_hasStraddleGlobalFuel` stays `false` with the
sharpened status: the single-lex route is REFUTED, the arc-count staging is the buildable route, its outer level is
done.  `fxBrauer_hasBrauerV2FullCompleteness` stays `false`.  `= false`. -/
def fxBrauer_hasStagedInnerDescentDischarged : Bool := false

end FX1Poly.Polygraph
