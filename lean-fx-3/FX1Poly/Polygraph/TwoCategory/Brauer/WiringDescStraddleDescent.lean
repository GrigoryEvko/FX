import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcDescent
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraighteningGap

/-! # BRAUER-MIDDLE r2 B2 — the `straddleCount` PRIMARY coordinate: the lex measure that DESCENDS on the straddle
(breaching the exact move r1 proved RESISTS `arcMeasure`)

r1's arc-descent round (`Brauer/WiringDescArcDescent.lean`) shipped the list-order lex measure `arcMeasure`
(`cupNonCupInversions` × radix + `cupPositionSum`) that strictly descends on the three disjoint-support / cup-cup
cup-sink moves, and PROVED it ASCENDS on the ADJACENT-STRADDLE cup slide `[cupAt 0, crossingAt 1] ↝ [cupAt 1,
crossingAt 0]` (`straddle_resists_arcMeasure`: `cupNonCupInversions` frozen at `1`, `cupPositionSum` `0 → 1`).  That
was the ONE resisting move — and the r2 arc-anchor round sharpened it further to "the anchored tail-block target does
not exist" because the r1 3-block datatype had no slot for a crossing cup.

## The r2 fix — the `topPerm` slots make the target REAL, so a distance measure has a real minimum

B1 (`Brauer/WiringDescArcExtractor.lean`) ships the `topPerm` slots: `[cupAt 1, crossingAt 0] = standardFormWordExt5
{ cupBlock := [1], topPerm := [0] }` now EXISTS and is the straddle's extended standard form.  So the straddle's RHS
IS its standard form, and a distance-to-standard-form measure has a genuine minimum at `0`.  This file supplies the
PRIMARY coordinate that realizes that: the **straddle count** — the number of adjacent windows where a cup is
immediately followed by a CROSSING at exactly the cup's position `+ 1` (the `cupSlideRelation` LHS shape).  It reads
the crossing's OFFSET relative to the cup, NOT its list position, so it structurally evades the exact list-order
obstruction `straddle_resists_arcMeasure` was proven for.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`straddleCount`** — the primary coordinate: `+ 1` per adjacent `(cup, crossing-at-cup+1)` window (overlapping
    windows counted by recursion on the tail).
  * ★ **the straddle PRIMARY strictly descends** (`straddleCount_straddle_lt`): `straddleCount [cupAt 1, crossingAt 0]
    < straddleCount [cupAt 0, crossingAt 1]` (`0 < 1`) — the EXACT move r1's `arcMeasure` ascended on now DESCENDS on
    the new primary.  This is the straddle-onto-`topPerm` rung the recon named.
  * the three distant cup-sink moves HOLD `straddleCount` at `0` (`straddleCount_distant*_held`), so the r1
    `arcMeasure` (secondary) governs them unchanged.
  * **`straddleLexMeasure`** — the mixed-radix `Nat` embedding of the lex pair `(straddleCount, arcMeasure)`, with the
    two combine lemmas (`straddleLex_lt_of_primary` / `straddleLex_lt_of_secondary`) turning a lex descent into a
    strict `Nat` fuel decrease.
  * ★ **the full per-move lex descent table** (`straddleLex_straddle_lt` + the three `straddleLex_distant*_lt`): ALL
    FOUR shipped cup-sink moves strictly descend `straddleLexMeasure` — the straddle via the PRIMARY, the three
    distant slides via the SECONDARY (r1's `arcMeasure`).  So the lex pair covers every shipped cup-sink move,
    including the one r1 proved resists — the per-move descent obstruction is CLOSED.
  * the NON-VACUITY: the straddle IS a `BrauerConvFree8` move AND `straddleLexMeasure` strictly descends on it while
    `arcMeasure` alone ascends (`straddle_lex_descends_where_arcMeasure_ascends`, bundling `straddle_isMove` +
    `straddle_resists_arcMeasure`).

## The honest residual (feeds B3 / B4)

`straddleCount` is clean per-move (each shipped two-atom move in isolation), but is NOT globally frozen by every
distant slide against an ARBITRARY suffix: a distant cup-past-crossing slide can re-expose a straddle window
downstream (a `crossingAt (p+1)` already in the suffix).  Assembling `(straddleCount, arcMeasure)` into ONE
well-founded `Nat`-fuel monovariant over ARBITRARY interleavings — not just the clean per-move windows — is the
genuine remaining descent work.  It is now a COMPOSITION problem over a proven per-move table, not a "no measure
exists" wall.  `fxBrauer_hasBrauerV2FullCompleteness` stays `false`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The straddle-count primary coordinate -/

/-- ★ **The PRIMARY descent coordinate — the straddle count.**  The number of adjacent windows where a cup is
immediately followed by a CROSSING whose position is exactly the cup's position `+ 1` (the `cupSlideRelation` LHS
shape `[cupAt p, crossingAt (p+1)]`).  Overlapping windows are counted by recursing on the tail (keeping the second
atom).  It reads the crossing's OFFSET relative to the cup, NOT its list position, so it is NOT a list-order measure
— which is exactly why it evades the `straddle_resists_arcMeasure` obstruction (proven only for list-order
coordinates). -/
def straddleCount : List BrauerAtom → Nat
  | [] => 0
  | [_] => 0
  | first :: second :: rest =>
      cond (isCupAtom first && isCrossingAtom second && Nat.beq second.position (first.position + 1)) 1 0
        + straddleCount (second :: rest)

/-! ## The straddle primary strictly descends; the distant moves hold it -/

/-- The straddle LHS `[cupAt 0, crossingAt 1]` has straddle count `1` — the cup at `0` is immediately followed by a
crossing at `0 + 1`. -/
theorem straddleCount_straddle_lhs : straddleCount [cupAt 0, crossingAt 1] = 1 := by decide

/-- The straddle RHS `[cupAt 1, crossingAt 0]` has straddle count `0` — the crossing is to the LEFT of the cup's
position (`0 ≠ 1 + 1`), a `topPerm` routing, not a straddle window. -/
theorem straddleCount_straddle_rhs : straddleCount [cupAt 1, crossingAt 0] = 0 := by decide

/-- ★★ **The straddle PRIMARY strictly descends — the exact move r1's `arcMeasure` ascended on.**
`straddleCount [cupAt 1, crossingAt 0] < straddleCount [cupAt 0, crossingAt 1]` (`0 < 1`).  Where
`straddle_resists_arcMeasure` proved the list-order measure ascends on this move, the OFFSET-reading primary DESCENDS
— the straddle-onto-`topPerm` rung. -/
theorem straddleCount_straddle_lt :
    straddleCount [cupAt 1, crossingAt 0] < straddleCount [cupAt 0, crossingAt 1] := by decide

/-- The distant cup-past-cap move `[cupAt 0, capAt 2] ↝ [capAt 0, cupAt 0]` HOLDS the straddle count at `0` (a cap is
not a crossing, so no straddle window on either side). -/
theorem straddleCount_distantCupCap_held :
    straddleCount [capAt 0, cupAt 0] = straddleCount [cupAt 0, capAt 2] := by decide

/-- The distant cup-past-crossing move `[cupAt 0, crossingAt 2] ↝ [crossingAt 0, cupAt 0]` HOLDS the straddle count at
`0` (the crossing sits at offset `2`, not `cup + 1`, and on the RHS the crossing precedes the cup). -/
theorem straddleCount_distantCupCrossing_held :
    straddleCount [crossingAt 0, cupAt 0] = straddleCount [cupAt 0, crossingAt 2] := by decide

/-- The distant cup-past-cup move `[cupAt 0, cupAt 2] ↝ [cupAt 0, cupAt 0]` HOLDS the straddle count at `0` (both
operands are cups, neither a crossing). -/
theorem straddleCount_distantCupCup_held :
    straddleCount [cupAt 0, cupAt 0] = straddleCount [cupAt 0, cupAt 2] := by decide

/-! ## The lex measure (straddleCount primary, arcMeasure secondary) + the combine lemmas -/

/-- ★ **The mixed-radix `Nat` embedding of the lex pair `(straddleCount, arcMeasure)`.**  With `primaryRadix` chosen
above every reachable `arcMeasure`, this is a strictly-decreasing `Nat` fuel whose PRIMARY digit is the offset-reading
straddle count and whose SECONDARY digit is r1's list-order `arcMeasure`. -/
def straddleLexMeasure (primaryRadix secondaryRadix : Nat) (word : List BrauerAtom) : Nat :=
  straddleCount word * primaryRadix + arcMeasure secondaryRadix word

/-- Multiplication-free `(multiplier + 1) · radix = multiplier · radix + radix`. -/
private theorem succMulStraddle (multiplier radix : Nat) :
    (multiplier + 1) * radix = multiplier * radix + radix := by
  rw [Nat.mul_comm (multiplier + 1) radix, Nat.mul_succ, Nat.mul_comm radix multiplier]

/-- ★ **Primary drop ⟹ `straddleLexMeasure` drop** (given the secondary `arcMeasure` of the after-word is below the
primary radix). -/
theorem straddleLex_lt_of_primary (primaryRadix secondaryRadix : Nat) (wordAfter wordBefore : List BrauerAtom)
    (primLt : straddleCount wordAfter < straddleCount wordBefore)
    (secBound : arcMeasure secondaryRadix wordAfter < primaryRadix) :
    straddleLexMeasure primaryRadix secondaryRadix wordAfter
      < straddleLexMeasure primaryRadix secondaryRadix wordBefore := by
  have blockLe : straddleCount wordAfter * primaryRadix + primaryRadix
      ≤ straddleCount wordBefore * primaryRadix := by
    rw [← succMulStraddle]
    exact Nat.mul_le_mul_right primaryRadix primLt
  have belowBlock : straddleCount wordAfter * primaryRadix + arcMeasure secondaryRadix wordAfter
      < straddleCount wordAfter * primaryRadix + primaryRadix :=
    Nat.add_lt_add_left secBound _
  show straddleCount wordAfter * primaryRadix + arcMeasure secondaryRadix wordAfter
     < straddleCount wordBefore * primaryRadix + arcMeasure secondaryRadix wordBefore
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le belowBlock blockLe) (Nat.le_add_right _ _)

/-- ★ **Primary held + secondary `arcMeasure` drop ⟹ `straddleLexMeasure` drop** (no radix bound needed). -/
theorem straddleLex_lt_of_secondary (primaryRadix secondaryRadix : Nat) (wordAfter wordBefore : List BrauerAtom)
    (primEq : straddleCount wordAfter = straddleCount wordBefore)
    (secLt : arcMeasure secondaryRadix wordAfter < arcMeasure secondaryRadix wordBefore) :
    straddleLexMeasure primaryRadix secondaryRadix wordAfter
      < straddleLexMeasure primaryRadix secondaryRadix wordBefore := by
  show straddleCount wordAfter * primaryRadix + arcMeasure secondaryRadix wordAfter
     < straddleCount wordBefore * primaryRadix + arcMeasure secondaryRadix wordBefore
  rw [primEq]
  exact Nat.add_lt_add_left secLt _

/-! ## The full per-move lex descent table — all four shipped cup-sink moves descend -/

/-- ★★ **The straddle descends the lex measure via the PRIMARY.**  `straddleLexMeasure 16 8` strictly drops on the
straddle move `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` — the primary drops `1 → 0` (the `16` block
dominates), the secondary `arcMeasure 8` of the after-word (`= 9`) sits below the primary radix `16`.  This is the
move r1's `arcMeasure` alone ASCENDED on. -/
theorem straddleLex_straddle_lt :
    straddleLexMeasure 16 8 [cupAt 1, crossingAt 0] < straddleLexMeasure 16 8 [cupAt 0, crossingAt 1] :=
  straddleLex_lt_of_primary 16 8 [cupAt 1, crossingAt 0] [cupAt 0, crossingAt 1]
    straddleCount_straddle_lt (by decide)

/-- ★ **The distant cup-past-cap slide descends the lex measure via the SECONDARY** (primary held, `arcMeasure`
drops). -/
theorem straddleLex_distantCupCap_lt :
    straddleLexMeasure 16 8 [capAt 0, cupAt 0] < straddleLexMeasure 16 8 [cupAt 0, capAt 2] :=
  straddleLex_lt_of_secondary 16 8 [capAt 0, cupAt 0] [cupAt 0, capAt 2]
    straddleCount_distantCupCap_held (by decide)

/-- ★ **The distant cup-past-crossing slide descends the lex measure via the SECONDARY.** -/
theorem straddleLex_distantCupCrossing_lt :
    straddleLexMeasure 16 8 [crossingAt 0, cupAt 0] < straddleLexMeasure 16 8 [cupAt 0, crossingAt 2] :=
  straddleLex_lt_of_secondary 16 8 [crossingAt 0, cupAt 0] [cupAt 0, crossingAt 2]
    straddleCount_distantCupCrossing_held (by decide)

/-- ★ **The distant cup-past-cup slide descends the lex measure via the SECONDARY.** -/
theorem straddleLex_distantCupCup_lt :
    straddleLexMeasure 16 8 [cupAt 0, cupAt 0] < straddleLexMeasure 16 8 [cupAt 0, cupAt 2] :=
  straddleLex_lt_of_secondary 16 8 [cupAt 0, cupAt 0] [cupAt 0, cupAt 2]
    straddleCount_distantCupCup_held (by decide)

/-! ## Non-vacuity — the straddle is a genuine move on which the lex descends but arcMeasure ascends -/

/-- ★★ **The straddle: a genuine `BrauerConvFree8` move on which the lex measure DESCENDS while `arcMeasure` ASCENDS.**
Bundles: (i) the straddle is a real presentation move (`straddle_isMove`); (ii) `straddleLexMeasure` strictly descends
on it (`straddleLex_straddle_lt`); (iii) r1's list-order `cupPositionSum` (hence `arcMeasure`) strictly ASCENDS on it
(`straddle_resists_arcMeasure.2`).  This is the exact rebuttal: the new primary coordinate resolves the one move the
r1 measure could not. -/
theorem straddle_lex_descends_where_arcMeasure_ascends :
    BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0]
      ∧ straddleLexMeasure 16 8 [cupAt 1, crossingAt 0] < straddleLexMeasure 16 8 [cupAt 0, crossingAt 1]
      ∧ cupPositionSum [cupAt 0, crossingAt 1] < cupPositionSum [cupAt 1, crossingAt 0] :=
  ⟨straddle_isMove, straddleLex_straddle_lt, straddle_resists_arcMeasure.2⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the `straddleCount` PRIMARY lex measure DESCENDS on EVERY shipped cup-sink move (B2).**  The
straddle count `straddleCount` reads the crossing's offset relative to the cup, so it strictly DESCENDS on the
adjacent-straddle cup slide (`straddleCount_straddle_lt`, `1 → 0`) — the EXACT move r1's list-order `arcMeasure`
provably ASCENDED on (`straddle_resists_arcMeasure`) — and is HELD by the three distant cup-sink moves
(`straddleCount_distant*_held`), on which r1's `arcMeasure` (the secondary) still descends.  The lex embedding
`straddleLexMeasure` + the combine lemmas turn each into a strict `Nat` fuel decrease, and the full per-move table
(`straddleLex_straddle_lt` + `straddleLex_distant*_lt`) descends on ALL FOUR shipped moves — the per-move descent
obstruction the pass-5-arc wall named is CLOSED.  `= true`. -/
def fxBrauer_hasStraddleLexDescent : Bool := true

/-- **Honesty WALL marker — the GLOBAL single-fuel monovariant over arbitrary interleavings is NOT built (the B2
residual).**  `straddleCount` is clean per-move (each shipped two-atom move in isolation) but is NOT globally frozen
by every distant slide against an ARBITRARY suffix: a distant cup-past-crossing slide can re-expose a straddle window
downstream (a `crossingAt (p+1)` already in the suffix).  Composing `(straddleCount, arcMeasure)` into ONE
well-founded `Nat`-fuel monovariant over arbitrary interleavings — the fuel the full fold consumes — is the genuine
remaining descent work; it is now a COMPOSITION problem over a proven per-move table, not a "no measure exists" wall.
`fxBrauer_hasBrauerV2FullCompleteness` stays `false`.  `= false`. -/
def fxBrauer_hasStraddleGlobalFuel : Bool := false

end FX1Poly.Polygraph
