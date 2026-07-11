import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFold

/-! # BRAUER r32 — the INTERLEAVED-arc witness: a genuine `i<k<j<l` cup/cap word reaches its corrected
standard form, the fourth (straddle) sink rung, and the clean-boundary decomposition of the global monovariant

The pass-5-arc wall (`Brauer/WiringDescCrossingComplete.lean`) caps the free-Brauer straightening at the
INTERLEAVED-arc configuration `i < k < j < l` — a cup forced past a straddling cap — where the list-order measure is
frozen across the commute.  r3 (`Brauer/WiringDescCorrectedFold.lean`) shipped `correctedFold_straddle_reaches`: the
PURE straddle `[cupAt 0, crossingAt 1]` reaches its corrected form via one cup-slide.  This file lands the next honest
rung: a genuinely INTERLEAVED word (a cup and a cap with a straddling crossing BETWEEN them) whose full corrected
standard form is reached by a machine-checked THREE-move `BrauerConvFree8` chain — the exact `i<k<j<l` class the wall
names, discharged on a concrete witness.

## The witness (truth-probed first)

`W = [cupAt 0, crossingAt 1, capAt 2]` on 2 bottom wires.  Its diagram is the single crossing
`{ bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0] }` (`interleavedArc_diagramEq_singleCrossing`, kernel
`decide`), and its corrected extended standard form is exactly `[crossingAt 0]` — so the reach TARGET is real and the
extractor realizes it.  The word is genuinely interleaved: the cup produces a pair, the crossing straddles its right
leg with the through-strand, and the cap consumes the crossed leg with the far wire — a cup and a cap that are NOT
disjoint (the crossing sits between them), the minimal `i<k<j<l` cup/cap straddle.

## What this file ships (each zero-axiom, structural / `decide` on closed literals)

  * ★★ **`brauerConvFree8_interleavedArc_reachesCorrectedForm`** — the flagship: `W` is `BrauerConvFree8`-convertible
    to `standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf 2 W))` (= `[crossingAt 0]`) via a
    THREE-move whisker-free chain — (1) the straddle cup-slide sinks the cup past the crossing
    (`[cupAt 0, crossingAt 1, capAt 2] ~ [cupAt 1, crossingAt 0, capAt 2]`), (2) the interchange commutes the now-distant
    crossing past the cap (`~ [cupAt 1, capAt 2, crossingAt 0]`), (3) the mirror snake deletes the exposed cup/cap
    (`~ [crossingAt 0]`).  It threads ONLY the free `BrauerConvFree8` constructors + `ofFree` — never
    `BrauerConv.whisker` (the anti-circularity discipline).
  * ★ **`brauerConvFree8_interleavedArc_straddleStep`** — the load-bearing FIRST move exhibited alone: the straddle
    cup-slide fires inside the interleaved word.
  * ★ **`arcSink_straddle`** — the FOURTH Σ-carried sink rung (the three shipped in `Brauer/WiringDescArcDescentFold`
    cover only the disjoint / cup-cup slides): extends a running `BrauerConvFree8` accumulator across the
    adjacent-straddle cup-slide in arbitrary context AND certifies the `straddleLexMeasure` drop (the PRIMARY straddle
    coordinate descending, given the per-move `straddleCount` drop the residual composition supplies).
  * **`arcSink_straddle_clean`** — the concrete clean instance discharging the drop hypothesis via
    `straddleCount_straddle_lt`.
  * ★ **`straddleCount_append_decomposes`** — the boundary decomposition of the global monovariant:
    `straddleCount (leftWord ++ rightWord) = straddleCount leftWord + (straddleBoundaryCount leftWord rightWord +
    straddleCount rightWord)`, isolating the ONE boundary-window term `straddleBoundaryCount` a distant slide can
    re-expose, and its clean corollary `straddleCount_isAdditive_ofCleanBoundary`.  This is the honest first slice of
    the "COMPOSITION problem over a proven per-move table" the r2 straddle residual named — it pins the exact extra
    term the global monovariant must control.

## The honest residual — the exact jamming sub-case (named IN this file, no new ledger)

The full free-Brauer straightening `BrauerExt5CorrectedFoldReaches` (every word reaches its corrected form) is NOT
discharged.  The three-move chain here is HAND-BUILT for the width-2 witness; the GENERAL interleaved `i<k<j<l` fold
needs the global single-`Nat`-fuel monovariant over ARBITRARY interleavings (the `straddleBoundaryCount`
re-exposure term made globally well-founded — `straddleCount_append_decomposes` isolates it but does not bound it) OR
the arc-insertion recursion (the `recCombConv` arc analog), threaded by a whisker-free driver.  That is the r33
target.  So `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, and
`fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`; #2013 does NOT close.  Every residual is a route / measure
gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin; independent `#print axioms` clean. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## B1 — the interleaved-arc witness reaches its corrected standard form -/

/-- The interleaved witness `[cupAt 0, crossingAt 1, capAt 2]` induces the single-crossing diagram
`{ bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0] }` — the same diagram as the bare `[crossingAt 0]`.
Kernel-decided; confirms the reach target is a genuine diagram identity before any presentation move fires. -/
theorem interleavedArc_diagramEq_singleCrossing :
    brauerDiagramOf 2 [cupAt 0, crossingAt 1, capAt 2] = brauerDiagramOf 2 [crossingAt 0] := by decide

/-- ★ **The load-bearing straddle step, inside the interleaved word.**  The adjacent-straddle cup-slide sinks the cup
one place past the straddling crossing while the cap rides along as context:
`[cupAt 0, crossingAt 1, capAt 2] ~ [cupAt 1, crossingAt 0, capAt 2]`.  This is the exact move the pass-5-arc wall is
about, fired in the genuinely interleaved word — the first of the three-move reach. -/
theorem brauerConvFree8_interleavedArc_straddleStep :
    BrauerConvFree8 [cupAt 0, crossingAt 1, capAt 2] [cupAt 1, crossingAt 0, capAt 2] :=
  BrauerConvFree8.whiskerRight [capAt 2] (BrauerConvFree8.cupSlide 0)

/-- ★★ **THE INTERLEAVED-ARC REACH.**  The genuinely interleaved word `W = [cupAt 0, crossingAt 1, capAt 2]` (a cup
and a cap with a straddling crossing between them — the minimal `i<k<j<l` cup/cap straddle) is
`BrauerConvFree8`-convertible to the corrected extended standard form of its own diagram
(`standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf 2 W))`, which computes to
`[crossingAt 0]`).  The three-move whisker-free chain:

  1. **straddle cup-slide** — `[cupAt 0, crossingAt 1, capAt 2] ~ [cupAt 1, crossingAt 0, capAt 2]`
     (`BrauerConvFree8.cupSlide 0` whiskered by the trailing cap);
  2. **interchange** — the now-distant crossing at `0` and cap at `2` commute:
     `[cupAt 1, crossingAt 0, capAt 2] ~ [cupAt 1, capAt 2, crossingAt 0]`
     (`BrauerConvFree.interchange 0 2 crossingWiring capWiring` whiskered by the leading cup);
  3. **mirror snake** — the exposed adjacent cup/cap `[cupAt 1, capAt 2]` deletes:
     `[cupAt 1, capAt 2, crossingAt 0] ~ [crossingAt 0]` (`BrauerConvFree.snakeMirror 1` whiskered by the trailing
     crossing).

Threads ONLY the free constructors — never `BrauerConv.whisker` / `brauerConv_complete`.  This is
`BrauerExt5CorrectedFoldReaches` instantiated and DISCHARGED on the interleaved class the wall names. -/
theorem brauerConvFree8_interleavedArc_reachesCorrectedForm :
    BrauerConvFree8 [cupAt 0, crossingAt 1, capAt 2]
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected
        (brauerDiagramOf 2 [cupAt 0, crossingAt 1, capAt 2]))) := by
  have hform :
      standardFormWordExt5 (reconstructStandardFormExt5Corrected
        (brauerDiagramOf 2 [cupAt 0, crossingAt 1, capAt 2])) = [crossingAt 0] := by decide
  rw [hform]
  exact BrauerConvFree8.trans
    (BrauerConvFree8.whiskerRight [capAt 2] (BrauerConvFree8.cupSlide 0))
    (BrauerConvFree8.trans
      (BrauerConvFree8.whiskerLeft [cupAt 1]
        (brauerConvFree8_ofFree
          (BrauerConvFree.interchange 0 2 crossingWiring capWiring (by decide))))
      (BrauerConvFree8.whiskerRight [crossingAt 0]
        (brauerConvFree8_ofFree (BrauerConvFree.snakeMirror 1))))

/-! ## B2 — the fourth (straddle) Σ-carried sink rung -/

/-- ★ **The straddle sink rung.**  Extends a running `BrauerConvFree8` accumulator from `startWord` across the
adjacent-straddle cup-slide `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` in arbitrary horizontal + vertical
context, AND certifies the strict `straddleLexMeasure` drop — the PRIMARY straddle coordinate descending.  The
per-move `straddleCount` drop (`primDrop`) is taken as a hypothesis: in the clean two-atom window it is
`straddleCount_straddle_lt`; over an arbitrary suffix it is exactly the term the global monovariant composition must
supply (the r33 residual).  This is the FOURTH `arcSink_*` rung — the three shipped in
`Brauer/WiringDescArcDescentFold` cover only the disjoint / cup-cup slides. -/
theorem arcSink_straddle (primaryRadix secondaryRadix : Nat)
    (startWord prefixWord suffixWord : List BrauerAtom)
    (conv : BrauerConvFree8 startWord (prefixWord ++ ([cupAt 0, crossingAt 1] ++ suffixWord)))
    (secBound : arcMeasure secondaryRadix (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord)) < primaryRadix)
    (primDrop : straddleCount (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
        < straddleCount (prefixWord ++ ([cupAt 0, crossingAt 1] ++ suffixWord))) :
    BrauerConvFree8 startWord (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
      ∧ straddleLexMeasure primaryRadix secondaryRadix (prefixWord ++ ([cupAt 1, crossingAt 0] ++ suffixWord))
          < straddleLexMeasure primaryRadix secondaryRadix (prefixWord ++ ([cupAt 0, crossingAt 1] ++ suffixWord)) :=
  ⟨conv.trans (cupSlideStraddleFree8_inContext prefixWord suffixWord 0),
   straddleLex_lt_of_primary primaryRadix secondaryRadix _ _ primDrop secBound⟩

/-- ★ **The clean straddle rung** — the two-atom window in isolation: the per-move `straddleCount` drop is discharged
by `straddleCount_straddle_lt`, so no drop hypothesis is needed.  The concrete instance of `arcSink_straddle` at empty
context. -/
theorem arcSink_straddle_clean (primaryRadix secondaryRadix : Nat) (startWord : List BrauerAtom)
    (conv : BrauerConvFree8 startWord [cupAt 0, crossingAt 1])
    (secBound : arcMeasure secondaryRadix [cupAt 1, crossingAt 0] < primaryRadix) :
    BrauerConvFree8 startWord [cupAt 1, crossingAt 0]
      ∧ straddleLexMeasure primaryRadix secondaryRadix [cupAt 1, crossingAt 0]
          < straddleLexMeasure primaryRadix secondaryRadix [cupAt 0, crossingAt 1] :=
  ⟨conv.trans brauerConvFree8_cupSlide_derivable,
   straddleLex_lt_of_primary primaryRadix secondaryRadix _ _ straddleCount_straddle_lt secBound⟩

/-! ## B3 — the boundary decomposition of the global straddle monovariant -/

/-- One straddle window bit: `1` when `first` is a cup immediately followed by a crossing at exactly `first + 1`
(the `cupSlideRelation` LHS shape), else `0`.  Byte-identical to the head test inside `straddleCount`. -/
def straddleWindowBit (first second : BrauerAtom) : Nat :=
  cond (isCupAtom first && isCrossingAtom second && Nat.beq second.position (first.position + 1)) 1 0

/-- The straddle windows that an append `leftWord ++ rightWord` creates ACROSS the boundary — the single window
formed by the last atom of `leftWord` and the first atom of `rightWord` (recursing to the last atom of `leftWord`).
This is the ONE term a distant slide against an arbitrary suffix can re-expose. -/
def straddleBoundaryCount : List BrauerAtom → List BrauerAtom → Nat
  | [], _ => 0
  | [singleLeft], rightWord =>
      match rightWord with
      | [] => 0
      | firstRight :: _ => straddleWindowBit singleLeft firstRight
  | _ :: secondLeft :: restLeft, rightWord => straddleBoundaryCount (secondLeft :: restLeft) rightWord

/-- ★ **The straddle-count append decomposition.**  `straddleCount` splits over an append as the left count, plus the
single boundary window, plus the right count:
`straddleCount (leftWord ++ rightWord) = straddleCount leftWord + (straddleBoundaryCount leftWord rightWord
+ straddleCount rightWord)`.  Structural induction on `leftWord` with two-atom lookahead.  This isolates EXACTLY the
extra term (`straddleBoundaryCount`) the global monovariant must control — the honest first slice of the composition
problem the r2 straddle residual named. -/
theorem straddleCount_append_decomposes : (leftWord rightWord : List BrauerAtom) →
    straddleCount (leftWord ++ rightWord)
      = straddleCount leftWord + (straddleBoundaryCount leftWord rightWord + straddleCount rightWord)
  | [], rightWord => by
      show straddleCount rightWord = 0 + (0 + straddleCount rightWord)
      rw [Nat.zero_add, Nat.zero_add]
  | [singleLeft], rightWord => by
      cases rightWord with
      | nil => rfl
      | cons firstRight restRight =>
          show straddleWindowBit singleLeft firstRight + straddleCount (firstRight :: restRight)
            = 0 + (straddleWindowBit singleLeft firstRight + straddleCount (firstRight :: restRight))
          exact (Nat.zero_add _).symm
  | headLeft :: secondLeft :: restLeft, rightWord => by
      show straddleWindowBit headLeft secondLeft + straddleCount ((secondLeft :: restLeft) ++ rightWord)
        = straddleWindowBit headLeft secondLeft + straddleCount (secondLeft :: restLeft)
          + (straddleBoundaryCount (secondLeft :: restLeft) rightWord + straddleCount rightWord)
      rw [straddleCount_append_decomposes (secondLeft :: restLeft) rightWord]
      exact (Nat.add_assoc _ _ _).symm

/-- ★ **The clean-boundary corollary.**  When the append creates no boundary straddle window
(`straddleBoundaryCount leftWord rightWord = 0`), `straddleCount` is additive over the append — the fragment on which
the global monovariant is already frozen (a distant slide that does not re-expose a downstream window). -/
theorem straddleCount_isAdditive_ofCleanBoundary (leftWord rightWord : List BrauerAtom)
    (cleanBoundary : straddleBoundaryCount leftWord rightWord = 0) :
    straddleCount (leftWord ++ rightWord) = straddleCount leftWord + straddleCount rightWord := by
  rw [straddleCount_append_decomposes leftWord rightWord, cleanBoundary, Nat.zero_add]

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — a genuinely INTERLEAVED cup/cap word reaches its corrected standard form (B1).**  The
minimal `i<k<j<l` cup/cap straddle `[cupAt 0, crossingAt 1, capAt 2]` (a cup and a cap with a straddling crossing
between them) is `BrauerConvFree8`-convertible to the corrected extended standard form of its diagram (`[crossingAt 0]`)
via a machine-checked THREE-move whisker-free chain — straddle cup-slide, interchange, mirror snake
(`brauerConvFree8_interleavedArc_reachesCorrectedForm`).  The reach target is a real diagram identity
(`interleavedArc_diagramEq_singleCrossing`) and goes THROUGH the exact straddle move the pass-5-arc wall names
(`brauerConvFree8_interleavedArc_straddleStep`).  This is `BrauerExt5CorrectedFoldReaches` discharged on the
interleaved class — one witness, not the general fold.  `= true`. -/
def fxBrauer_hasInterleavedArcWitness : Bool := true

/-- ★ **Honesty marker — the FOURTH (straddle) Σ-carried sink rung ships (B2).**  `arcSink_straddle` extends a running
`BrauerConvFree8` accumulator across the adjacent-straddle cup-slide in arbitrary context and certifies the
`straddleLexMeasure` PRIMARY drop, completing the per-move sink table the three disjoint / cup-cup rungs in
`Brauer/WiringDescArcDescentFold` left open; `arcSink_straddle_clean` is the concrete drop-free instance.  `= true`. -/
def fxBrauer_hasStraddleSinkRung : Bool := true

/-- ★ **Honesty marker — the boundary decomposition of the global straddle monovariant ships (B3).**
`straddleCount_append_decomposes` proves `straddleCount` splits over an append as `left + (boundaryWindow + right)`,
isolating the single `straddleBoundaryCount` term a distant slide can re-expose, with the clean corollary
`straddleCount_isAdditive_ofCleanBoundary` for the frozen fragment.  This pins the EXACT extra term the global
single-fuel monovariant must control — the honest first slice of the composition problem the r2 straddle residual
named.  `= true`. -/
def fxBrauer_hasStraddleBoundaryDecomposition : Bool := true

/-- **Honesty WALL marker — the GENERAL interleaved-arc fold is NOT built; #2013 does NOT close.**  The three-move
reach `brauerConvFree8_interleavedArc_reachesCorrectedForm` is HAND-BUILT for the width-2 witness.  The GENERAL
interleaved `i<k<j<l` straightening `BrauerExt5CorrectedFoldReaches` needs, jointly: the global single-`Nat`-fuel
monovariant over ARBITRARY interleavings — the `straddleBoundaryCount` re-exposure term
(`straddleCount_append_decomposes` isolates it but does not bound it) made well-founded — OR the arc-insertion
recursion (the `recCombConv` arc analog), threaded by a whisker-free driver.  That is the r33 target.  So
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, and `fxBrauer_hasBrauerV2FullCompleteness`
all STAY `false`.  A route / measure gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasInterleavedArcGlobalFold : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r32 terminal state — MACHINE-CHECKED.**  The three new ingredient markers are `true` (the
interleaved-arc reach, the fourth straddle sink rung, the boundary decomposition), on top of the shipped
`fxBrauer_hasStraddleLexDescent` (the per-move lex table) and `fxBrauer_hasCorrectedFoldReduction` (the whisker-free
assembly), while the global straddle fuel and all three completeness masters STAY `false`.  A `rfl`-conjunction the
kernel checks; no master flip is fabricated, #2013 does NOT close. -/
theorem fxBrauer_interleavedArcTerminalState :
    fxBrauer_hasInterleavedArcWitness = true
      ∧ fxBrauer_hasStraddleSinkRung = true
      ∧ fxBrauer_hasStraddleBoundaryDecomposition = true
      ∧ fxBrauer_hasStraddleLexDescent = true
      ∧ fxBrauer_hasCorrectedFoldReduction = true
      ∧ fxBrauer_hasStraddleGlobalFuel = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
