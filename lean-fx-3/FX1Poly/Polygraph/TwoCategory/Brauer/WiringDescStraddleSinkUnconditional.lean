import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescInterleavedArcWitness

/-! # BRAUER r33 — the straddle sink rung made UNCONDITIONAL: the r32 `primDrop` residual discharged, the
hypothesis-free straddle rung, and a two-cell `recComb`-arc reduction THROUGH the straddle

r32 (`Brauer/WiringDescInterleavedArcWitness.lean`) shipped `arcSink_straddle` — the fourth Σ-carried cup-sink rung —
but it takes the per-move `straddleCount` drop (`primDrop`) as a HYPOTHESIS, its own docstring naming that term "over
an arbitrary suffix … exactly the term the global monovariant composition must supply (the r33 residual)".  It also
shipped `straddleCount_append_decomposes`, isolating (not bounding) the single boundary window a distant slide can
re-expose.  This file discharges the `primDrop` residual as a THEOREM and upgrades the rung to be hypothesis-free.

## The r32 `primDrop` residual is a THEOREM (truth-probed on hostile contexts first)

The residual move is the ADJACENT-straddle cup-slide `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` — DISTINCT
from the distant cup-past-crossing slide whose re-exposure keeps the GLOBAL fuel open (route (a) below).  Probed over
hostile prefix / suffix contexts (`rhs = prefix ++ [cupAt 1, crossingAt 0] ++ suffix`, `lhs` the pre-slide word):
EVERY context gives `straddleCount rhs = straddleCount lhs − 1`, unconditionally.  Mechanism, all boundary bits `0`:
the adjacent-straddle slide changes `straddleCount` ONLY inside its own two-atom window (`1 → 0`); the prefix|window
boundary window has a CUP as its second atom (`straddleWindowBit _ (cupAt _) = 0`, `isCrossingAtom (cupAt _) = false`)
and the window|suffix boundary window has a CROSSING as its first atom (`isCupAtom (crossingAt _) = false`).  So
`primDrop` is provable from the shipped `straddleCount_append_decomposes`.

## What this file ships (each zero-axiom, structural / `decide` on closed literals — no `omega` / `simp`-AC /
`native_decide` / `WellFounded.fix`; per-declaration `#assert_no_axioms` in the audit twin)

  * **`straddleCount_crossingHead`** — a crossing head is never a straddle window, so it holds `straddleCount`
    (`straddleCount (crossingAt p :: suffix) = straddleCount suffix`).
  * **`straddleCount_cupCrossingCons`** — a `cup :: crossing :: suffix` word splits off its head window bit:
    `straddleCount (cupAt p :: crossingAt q :: suffix) = straddleWindowBit (cupAt p) (crossingAt q) + straddleCount suffix`.
  * **`straddleWindowBit_cupSecond_eq_zero`** — the boundary window a cup-headed right word forms with any left atom is
    `0` (its second atom is a cup, not a crossing).
  * **`straddleBoundaryCount_cupHead`** — the whole boundary count vanishes when the right word starts with a cup
    (structural recursion to the last left atom, closed by `straddleWindowBit_cupSecond_eq_zero`).
  * ★★ **`straddleCount_straddleSlide_drop`** — THE r32 residual, discharged: the per-move `straddleCount` drop for the
    offset-0 adjacent-straddle cup-slide in ARBITRARY prefix / suffix context, unconditionally.
  * ★ **`arcSink_straddle_unconditional`** — the fourth sink rung with `primDrop` REMOVED: it now needs only the running
    `BrauerConvFree8` accumulator and the `arcMeasure < primaryRadix` radix bound, exactly like the three distant rungs
    in `Brauer/WiringDescArcDescentFold`.  `arcSink_straddle_unconditional_clean` is the empty-context instance.
  * ★★ **`arcSinkFold_throughStraddle_demo`** — a genuine TWO-cell `recComb`-arc reduction that the `arcMeasure`-only
    fold could NOT perform (it jams where `arcMeasure` rises across the straddle): cell 1 is the adjacent-straddle
    cup-slide (`arcMeasure 8` RISES `18 → 19`), cell 2 a distant cup-cup slide (`arcMeasure` drops `19 → 17`), yet the
    lex fuel `straddleLexMeasure 64 8` STRICTLY descends on BOTH (`82 → 19 → 17`) — cell 1 via the PRIMARY (threading
    `straddleCount_straddleSlide_drop`, not a raw `decide`), cell 2 via the SECONDARY.  All three words are the same
    diagram (`decide`).

## The honest residual — the GLOBAL fuel is still unbounded (route (a), named IN this file, no new ledger)

The full free-Brauer straightening `BrauerExt5CorrectedFoldReaches` stays open.  Route (a) — one global `Nat` fuel over
ARBITRARY interleavings — is eval-refuted for the SHIPPED lex measure: the DISTANT cup-past-crossing slide
(`distantCupCrossingSlideFree8`, a real `BrauerConvFree8` move) re-exposes a downstream straddle window, and
`straddleLexMeasure 16 8` ASCENDS `16 → 24` across it (`[cupAt 0, crossingAt 2, crossingAt 1]` vs
`[crossingAt 0, cupAt 0, crossingAt 1]`, the SAME diagram) — the primary re-exposure dominates the secondary drop.  So
`(straddleCount, arcMeasure)` is provably NOT a global monovariant; the driver must sink straddles BEFORE the distant
redex re-exposes them (an ORDERING discipline), or a genuinely new potential is needed.  Route (b) — the ordered
arc-insertion driver over the full move-class case table — is the other ≥1-round path.  So
`fxBrauer_hasStraddleGlobalFuel`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, and
`fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`; this round is PURELY ADDITIVE, no master flips.  Every residual
is a route / measure gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A1 — the two straddle-count head reductions -/

/-- A crossing head is never the first atom of a straddle window (`isCupAtom (crossingAt _) = false`), so consing a
crossing onto a word HOLDS its straddle count: `straddleCount (crossingAt position :: suffixWord) = straddleCount
suffixWord`.  Structural `cases` on the suffix; the two-atom arm reduces the head `cond` to `0` by `rfl`. -/
theorem straddleCount_crossingHead (position : Nat) (suffixWord : List BrauerAtom) :
    straddleCount (crossingAt position :: suffixWord) = straddleCount suffixWord := by
  cases suffixWord with
  | nil => rfl
  | cons firstSuffix restSuffix =>
      show (0 : Nat) + straddleCount (firstSuffix :: restSuffix) = straddleCount (firstSuffix :: restSuffix)
      exact Nat.zero_add _

/-- A `cup :: crossing :: suffix` word splits its straddle count into the head window bit plus the count of the tail
after the crossing (which, by `straddleCount_crossingHead`, is just the count of the suffix):
`straddleCount (cupAt posCup :: crossingAt posCross :: suffixWord) = straddleWindowBit (cupAt posCup) (crossingAt
posCross) + straddleCount suffixWord`.  The head `cond` of `straddleCount` is byte-identical to `straddleWindowBit`. -/
theorem straddleCount_cupCrossingCons (posCup posCross : Nat) (suffixWord : List BrauerAtom) :
    straddleCount (cupAt posCup :: crossingAt posCross :: suffixWord)
      = straddleWindowBit (cupAt posCup) (crossingAt posCross) + straddleCount suffixWord := by
  show straddleWindowBit (cupAt posCup) (crossingAt posCross)
        + straddleCount (crossingAt posCross :: suffixWord)
      = straddleWindowBit (cupAt posCup) (crossingAt posCross) + straddleCount suffixWord
  rw [straddleCount_crossingHead]

/-! ## A2 — the boundary window of a cup-headed right word vanishes -/

/-- The boundary straddle window any left atom forms with a CUP-headed right word is `0`: a straddle window needs a
crossing as its SECOND atom (`isCrossingAtom (cupAt _) = false`).  `cases` on the left atom's cup-ness after rewriting
the middle conjunct to `false`. -/
theorem straddleWindowBit_cupSecond_eq_zero (first : BrauerAtom) (position : Nat) :
    straddleWindowBit first (cupAt position) = 0 := by
  show cond (isCupAtom first && isCrossingAtom (cupAt position)
      && Nat.beq (cupAt position).position (first.position + 1)) 1 0 = 0
  rw [show isCrossingAtom (cupAt position) = false from rfl]
  cases hCupFirst : isCupAtom first <;> rfl

/-- The whole boundary count vanishes when the right word starts with a cup: `straddleBoundaryCount prefixWord
(cupAt position :: rest) = 0`.  Structural recursion down `prefixWord` to its last atom, whose boundary window with the
leading cup is `0` by `straddleWindowBit_cupSecond_eq_zero`. -/
theorem straddleBoundaryCount_cupHead :
    (prefixWord : List BrauerAtom) → (position : Nat) → (rest : List BrauerAtom) →
    straddleBoundaryCount prefixWord (cupAt position :: rest) = 0
  | [], _, _ => rfl
  | [singleLeft], position, _ => straddleWindowBit_cupSecond_eq_zero singleLeft position
  | _ :: secondLeft :: restLeft, position, rest =>
      straddleBoundaryCount_cupHead (secondLeft :: restLeft) position rest

/-! ## A3 — THE r32 residual: the per-move straddle-count drop in arbitrary context -/

/-- ★★ **The r32 `primDrop` residual, discharged unconditionally.**  The offset-0 adjacent-straddle cup-slide
`[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` strictly DROPS `straddleCount` in ANY prefix / suffix context:
`straddleCount (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord)) < straddleCount (prefixWord ++ ([cupAt 0,
crossingAt 1] ++ suffixWord))`.  Both sides split by `straddleCount_append_decomposes`; the prefix|window boundary
vanishes (`straddleBoundaryCount_cupHead`, cup-headed windows), and the window itself contributes `0` (RHS,
`straddleWindowBit (cupAt 1) (crossingAt 0) = 0`, a `topPerm` routing) vs `1` (LHS, `straddleWindowBit (cupAt 0)
(crossingAt 1) = 1`, a genuine straddle) over the shared `straddleCount suffixWord`.  This is exactly the term r32's
`arcSink_straddle` took as a hypothesis. -/
theorem straddleCount_straddleSlide_drop (prefixWord suffixWord : List BrauerAtom) :
    straddleCount (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
      < straddleCount (prefixWord ++ ([cupAt 0, crossingAt 1] ++ suffixWord)) := by
  have hAfter : straddleCount (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
      = straddleCount prefixWord + straddleCount suffixWord := by
    rw [show ([cupAt 1, crossingAt 0] ++ suffixWord) = cupAt 1 :: crossingAt 0 :: suffixWord from rfl,
        straddleCount_append_decomposes prefixWord (cupAt 1 :: crossingAt 0 :: suffixWord),
        straddleBoundaryCount_cupHead prefixWord 1 (crossingAt 0 :: suffixWord),
        Nat.zero_add,
        straddleCount_cupCrossingCons 1 0 suffixWord,
        show straddleWindowBit (cupAt 1) (crossingAt 0) = 0 from rfl,
        Nat.zero_add]
  have hBefore : straddleCount (prefixWord ++ ([cupAt 0, crossingAt 1] ++ suffixWord))
      = straddleCount prefixWord + (1 + straddleCount suffixWord) := by
    rw [show ([cupAt 0, crossingAt 1] ++ suffixWord) = cupAt 0 :: crossingAt 1 :: suffixWord from rfl,
        straddleCount_append_decomposes prefixWord (cupAt 0 :: crossingAt 1 :: suffixWord),
        straddleBoundaryCount_cupHead prefixWord 0 (crossingAt 1 :: suffixWord),
        Nat.zero_add,
        straddleCount_cupCrossingCons 0 1 suffixWord,
        show straddleWindowBit (cupAt 0) (crossingAt 1) = 1 from rfl]
  rw [hAfter, hBefore]
  exact Nat.add_lt_add_left
    (by rw [Nat.add_comm 1 (straddleCount suffixWord)]; exact Nat.lt_succ_self _)
    (straddleCount prefixWord)

/-! ## B — the straddle sink rung, hypothesis-free -/

/-- ★ **The fourth sink rung, UNCONDITIONAL.**  r32's `arcSink_straddle` with the `primDrop` hypothesis discharged by
`straddleCount_straddleSlide_drop`: it now extends the running `BrauerConvFree8` accumulator across the adjacent-straddle
cup-slide in arbitrary context and certifies the `straddleLexMeasure` PRIMARY drop needing ONLY the `arcMeasure <
primaryRadix` radix bound — putting the straddle rung on equal footing with the three distant rungs of
`Brauer/WiringDescArcDescentFold`. -/
theorem arcSink_straddle_unconditional (primaryRadix secondaryRadix : Nat)
    (startWord prefixWord suffixWord : List BrauerAtom)
    (conv : BrauerConvFree8 startWord (prefixWord ++ ([cupAt 0, crossingAt 1] ++ suffixWord)))
    (secBound : arcMeasure secondaryRadix (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
        < primaryRadix) :
    BrauerConvFree8 startWord (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
      ∧ straddleLexMeasure primaryRadix secondaryRadix (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
          < straddleLexMeasure primaryRadix secondaryRadix (prefixWord ++ ([cupAt 0, crossingAt 1] ++ suffixWord)) :=
  arcSink_straddle primaryRadix secondaryRadix startWord prefixWord suffixWord conv secBound
    (straddleCount_straddleSlide_drop prefixWord suffixWord)

/-- ★ **The unconditional straddle rung at empty context** — the two-atom window in isolation, hypothesis-free apart
from the running accumulator and the radix bound. -/
theorem arcSink_straddle_unconditional_clean (primaryRadix secondaryRadix : Nat) (startWord : List BrauerAtom)
    (conv : BrauerConvFree8 startWord [cupAt 0, crossingAt 1])
    (secBound : arcMeasure secondaryRadix [cupAt 1, crossingAt 0] < primaryRadix) :
    BrauerConvFree8 startWord [cupAt 1, crossingAt 0]
      ∧ straddleLexMeasure primaryRadix secondaryRadix [cupAt 1, crossingAt 0]
          < straddleLexMeasure primaryRadix secondaryRadix [cupAt 0, crossingAt 1] :=
  arcSink_straddle_unconditional primaryRadix secondaryRadix startWord [] [] conv secBound

/-! ## C — a two-cell `recComb`-arc reduction THROUGH the straddle -/

/-- ★★ **A two-cell arc-sink fold that crosses the straddle.**  The `arcMeasure`-only fold (`arcSinkFold_demo`,
`Brauer/WiringDescArcDescentFold`) jams at the straddle because `arcMeasure` RISES there.  Here the word
`[cupAt 0, crossingAt 1, cupAt 4, cupAt 6]` is `BrauerConvFree8`-convertible to `[cupAt 1, crossingAt 0, cupAt 4,
cupAt 4]` (the same diagram, `decide`) via TWO cells — (1) the adjacent-straddle cup-slide sinks the cup past the
crossing (`cupSlideStraddleFree8_inContext [] [cupAt 4, cupAt 6] 0`), on which `arcMeasure 8` RISES `18 → 19`;
(2) a distant cup-cup slide at offset 4 (`distantCupCupSlideFree8 4 4`, whiskered by the leading `cup / crossing`),
on which `arcMeasure 8` DROPS `19 → 17`.  The lex fuel `straddleLexMeasure 64 8` STRICTLY descends on BOTH cells
(`82 → 19 → 17`): cell 1 via the PRIMARY (threading `straddleCount_straddleSlide_drop`, not a raw `decide`), cell 2 via
the SECONDARY.  This is the arc-level `recComb` chain the straddle blocked at `arcMeasure`. -/
theorem arcSinkFold_throughStraddle_demo :
    BrauerConvFree8 [cupAt 0, crossingAt 1, cupAt 4, cupAt 6] [cupAt 1, crossingAt 0, cupAt 4, cupAt 4]
      ∧ straddleLexMeasure 64 8 [cupAt 1, crossingAt 0, cupAt 4, cupAt 6]
          < straddleLexMeasure 64 8 [cupAt 0, crossingAt 1, cupAt 4, cupAt 6]
      ∧ straddleLexMeasure 64 8 [cupAt 1, crossingAt 0, cupAt 4, cupAt 4]
          < straddleLexMeasure 64 8 [cupAt 1, crossingAt 0, cupAt 4, cupAt 6] := by
  refine ⟨?_, ?_, ?_⟩
  · exact BrauerConvFree8.trans
      (cupSlideStraddleFree8_inContext [] [cupAt 4, cupAt 6] 0)
      (BrauerConvFree8.whiskerLeft [cupAt 1, crossingAt 0] (distantCupCupSlideFree8 4 4 (by decide)))
  · exact straddleLex_lt_of_primary 64 8
      [cupAt 1, crossingAt 0, cupAt 4, cupAt 6] [cupAt 0, crossingAt 1, cupAt 4, cupAt 6]
      (straddleCount_straddleSlide_drop [] [cupAt 4, cupAt 6]) (by decide)
  · exact straddleLex_lt_of_secondary 64 8
      [cupAt 1, crossingAt 0, cupAt 4, cupAt 4] [cupAt 1, crossingAt 0, cupAt 4, cupAt 6]
      (by decide) (by decide)

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the r32 `primDrop` residual is a THEOREM (A).**  The per-move `straddleCount` drop for the
offset-0 adjacent-straddle cup-slide in ARBITRARY prefix / suffix context (`straddleCount_straddleSlide_drop`) — the
exact term r32's `arcSink_straddle` took as a hypothesis — is discharged unconditionally from the shipped boundary
decomposition, via the cup-headed boundary vanishing (`straddleBoundaryCount_cupHead`) and the two-atom window drop
(`1 → 0`).  `= true`. -/
def fxBrauer_hasStraddlePrimDropDischarged : Bool := true

/-- ★ **Honesty marker — the fourth sink rung is now HYPOTHESIS-FREE (B).**  `arcSink_straddle_unconditional` removes
r32's `primDrop` hypothesis, so the straddle rung needs only the running `BrauerConvFree8` accumulator and the
`arcMeasure < primaryRadix` radix bound — identical shape to the three distant rungs of
`Brauer/WiringDescArcDescentFold`; `arcSink_straddle_unconditional_clean` is the empty-context instance.  `= true`. -/
def fxBrauer_hasStraddleSinkUnconditional : Bool := true

/-- ★★ **Honesty marker — a two-cell `recComb`-arc reduction crosses the straddle (C).**
`arcSinkFold_throughStraddle_demo` chains the adjacent-straddle cup-slide (on which `arcMeasure` RISES `18 → 19`) with a
distant cup-cup slide (on which `arcMeasure` drops `19 → 17`) into a single `BrauerConvFree8` reduction between two
words of the same diagram, with the lex fuel `straddleLexMeasure 64 8` strictly descending on BOTH cells (`82 → 19 →
17`) — the chain the `arcMeasure`-only fold could not perform.  `= true`. -/
def fxBrauer_hasArcSinkThroughStraddle : Bool := true

/-- **Honesty WALL marker — the GLOBAL single-fuel monovariant over arbitrary interleavings is STILL unbounded.**  The
per-move straddle drop is now unconditional, but the DISTANT cup-past-crossing slide (`distantCupCrossingSlideFree8`, a
real `BrauerConvFree8` move) re-exposes a downstream straddle window and `straddleLexMeasure 16 8` ASCENDS `16 → 24`
across it (`[cupAt 0, crossingAt 2, crossingAt 1]` vs `[crossingAt 0, cupAt 0, crossingAt 1]`, the SAME diagram) — the
primary re-exposure dominates the secondary drop.  So `(straddleCount, arcMeasure)` is provably NOT a global
monovariant; the full fold needs an ORDERING discipline (sink straddles before the distant redex re-exposes them) or a
genuinely new potential, and the ordered arc-insertion driver over the full move-class case table is a ≥1-round path.
So `fxBrauer_hasStraddleGlobalFuel`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, and
`fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`.  A route / measure gap, never a truth gap (Lehrer–Zhang
arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasStraddleGlobalFuelBounded : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r33 terminal state — MACHINE-CHECKED.**  The three new ingredient markers are `true` (the r32
`primDrop` residual discharged as a theorem, the hypothesis-free straddle sink rung, the two-cell reduction through the
straddle), on top of the shipped `fxBrauer_hasStraddleSinkRung`, `fxBrauer_hasStraddleLexDescent`, and
`fxBrauer_hasCorrectedFoldReduction`, while the global straddle fuel and all three completeness masters STAY `false`.
A `rfl`-conjunction the kernel checks; this round is purely additive, no master flip is fabricated. -/
theorem fxBrauer_straddleSinkUnconditionalTerminalState :
    fxBrauer_hasStraddlePrimDropDischarged = true
      ∧ fxBrauer_hasStraddleSinkUnconditional = true
      ∧ fxBrauer_hasArcSinkThroughStraddle = true
      ∧ fxBrauer_hasStraddleSinkRung = true
      ∧ fxBrauer_hasStraddleLexDescent = true
      ∧ fxBrauer_hasCorrectedFoldReduction = true
      ∧ fxBrauer_hasStraddleGlobalFuelBounded = false
      ∧ fxBrauer_hasStraddleGlobalFuel = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
