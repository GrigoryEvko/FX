import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraddleSinkUnconditional

/-! # BRAUER r34 — the LOCAL per-cup arc-insertion leg fuel: a distance-to-slot measure that DESCENDS on the exact
hostile chain where the r33 GLOBAL `straddleLexMeasure` was machine-REFUTED to ASCEND

r33 (`Brauer/WiringDescStraddleSinkUnconditional.lean`) discharged the fourth (straddle) sink rung unconditionally, but
its wall marker `fxBrauer_hasStraddleGlobalFuelBounded = false` records the honest NO-GO: the single GLOBAL lex measure
`(straddleCount, arcMeasure)` is provably NOT a monovariant — the DISTANT cup-past-crossing slide re-exposes a
downstream straddle window and `straddleLexMeasure 16 8` ASCENDS `16 → 24` across the concrete pair
`[cupAt 0, crossingAt 2, crossingAt 1]` vs `[crossingAt 0, cupAt 0, crossingAt 1]` (the SAME diagram).  r33 named the
resolution: sink straddles BEFORE the distant redex re-exposes them — an ORDERING discipline, realized by a LOCAL
per-cup measure that tracks only the ONE cup being sunk, not a global sum over ALL cups (which the re-exposure inflates).

## The r34 ingredient — the local leg fuel `legLexFuel`, truth-probed on the exact refuting chain

The global `straddleCount` counts EVERY adjacent straddle window; a distant slide re-exposes a downstream one, so the
sum rises.  The LOCAL fuel reads only the LEFTMOST cup: its distance to its cup-block slot (`atomsRightOfFirstCup`,
the count of atoms strictly right of the first cup — a genuine list-position monovariant for the ONE sinking cup) with
the leftmost cup's own straddle window as the tie-break (`straddleBitAtFirstCup`).  Truth-probed (`#eval`, all values
confirmed before proving) on the EXACT chain that refuted the global measure:

```
      [cup0, cross2, cross1]  ~~>  [cross0, cup0, cross1]  ~~>  [cross0, cup1, cross0]      (all one diagram)
  (atomsRight, straddleBit):    (2, 0)         (1, 1)                 (1, 0)
  legLexFuel 8 = right*8+bit:     16     >       9         >           8        STRICTLY DESCENDS
  straddleLexMeasure 16 8:        16     <      24                              (global) ASCENDS
```

Where the global lex ASCENDS `16 → 24` (its primary re-exposure dominates), the local leg fuel DESCENDS `16 > 9 > 8`:
cell 1 (distant cup-past-crossing) drops the PRIMARY (distance `2 → 1`), cell 2 (adjacent straddle) holds the primary
and drops the SECONDARY bit (`1 → 0`).  This is the ordering discipline made a measure.

## What this file ships (each zero-axiom, structural / `decide` on closed literals — no `omega` / `simp`-AC /
`native_decide` / `WellFounded.fix` / `propext`; per-declaration `#assert_no_axioms` in the audit twin)

  * **`atomsRightOfFirstCup` / `straddleBitAtFirstCup` / `legLexFuel`** — the LOCAL leg-fuel lex pair and its
    mixed-radix `Nat` embedding, with the two combine lemmas (`legLex_lt_of_primary` / `legLex_lt_of_secondary`, exact
    mirrors of the shipped `straddleLex_lt_of_*`) turning a lex descent into a strict `Nat` fuel decrease.
  * **`straddleBitAtFirstCup_le_one`** — the tie-break digit is `≤ 1`, so it sits below any radix `> 1` (the secBound
    for the primary combine lemma, discharged generically).
  * ★ **`atomsRightOfFirstCup_prefixCupless` / `_nonCupThenCup`** — the leftmost-cup distance read-off in ARBITRARY
    cupless-prefix context: when a prefix contains no cup, the first cup's distance is the count of the atoms after it,
    independent of how far right the prefix pushes it.  Standalone structural recursion on the prefix (NO
    `List.append_assoc`, which leaks `propext`).
  * ★★ **`legFuel_leftmostCupCrossing_lt` / `legFuel_leftmostCupCap_lt`** — the PRIMARY (distance) descent of a cup
    sunk past a distant crossing / cap, WHISKERED into arbitrary cupless-prefix + arbitrary suffix context: the general
    mechanism (not a width-3 coincidence) that the local fuel descends wherever the leftmost cup sinks past a non-cup.
  * ★★ **`legFuelFold_throughReexposure_demo`** — THE flagship: the three-word `BrauerConvFree8` reduction across the
    EXACT chain that refuted the global measure, with `legLexFuel 8` strictly descending on BOTH cells (`16 > 9 > 8`)
    AND the explicit contrast that `straddleLexMeasure 16 8` ASCENDS on cell 1 (`16 < 24`) — the arc-level `recComb`
    chain that BOTH shipped fuels (`arcMeasure` jams at the straddle, `straddleLexMeasure` jams at the re-exposure)
    could not perform, threading ONLY the free `BrauerConvFree8` constructors.
  * **`legFuel_perCell_drops`** — the three sinking cells each drop `legLexFuel 8` (cup/cap `8 → 0`, cup/crossing
    `8 → 0`, straddle `9 → 8`), and the sibling cup/cup reorder HOLDS the primary (not a leg-fuel cell — it is the
    within-cup-block reorder, governed separately).

## The honest wall — the general recursion + OUTER threading are UNBUILT (named IN this file, no new ledger)

The local leg fuel is the buildable INNER measure and its primary descent generalizes to arbitrary cupless-prefix
context, but the full INNER descent is NOT a discharged fold: (J1) the two-level assembly threading the OUTER
`arcCountFuel` (shipped, `fxBrauer_hasStagedArcCountFuel = true`) with this INNER leg fuel, peeling a completed arc and
proving placed arcs untouched; (J2) the cap-side ∗-dual sink (caps sink to the FRONT); (J3) the `bottomCount = 0`
all-cup/all-loop class; (J4) the whisker-free driver consuming a `DiagramType` and the R3-A connectivity roundtrip its
per-step guard needs.  So `fxBrauer_hasStagedInnerDescentDischarged` STAYS `false`, and the three completeness masters
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all
STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.  Every residual is a route / measure gap,
never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the local leg-fuel lex pair (distance-to-slot of the leftmost cup + its straddle tie-break) -/

/-- The number of atoms in a word (structural, `= List.length`, but propext-clean — it never invokes the
`List.length_append` lemma). -/
def countAtoms : List BrauerAtom → Nat
  | [] => 0
  | _ :: rest => 1 + countAtoms rest

/-- ★ **The PRIMARY leg coordinate — distance of the LEFTMOST cup to its slot.**  The count of atoms strictly to the
right of the FIRST cup in the word (`0` once the leftmost cup already sits at the tail).  Reads only the ONE cup being
sunk, so a distant slide re-exposing a DOWNSTREAM straddle window does NOT inflate it — the exact defect that made the
global `straddleCount` sum ASCEND. -/
def atomsRightOfFirstCup : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => cond (isCupAtom atom) (countAtoms rest) (atomsRightOfFirstCup rest)

/-- ★ **The SECONDARY leg coordinate — the straddle window bit at the LEFTMOST cup.**  `1` when the first cup is
immediately followed by a crossing at exactly its position `+ 1` (a genuine straddle), else `0`.  The tie-break that
descends on the pure straddle relabel (which holds the primary distance). -/
def straddleBitAtFirstCup : List BrauerAtom → Nat
  | [] => 0
  | [_] => 0
  | first :: second :: rest =>
      cond (isCupAtom first) (straddleWindowBit first second) (straddleBitAtFirstCup (second :: rest))

/-- ★ **The mixed-radix `Nat` embedding of the local leg lex pair** `(atomsRightOfFirstCup, straddleBitAtFirstCup)`.
With `radix > 1` (the tie-break bit is `≤ 1`), a lex descent is a strict `Nat` fuel decrease. -/
def legLexFuel (radix : Nat) (word : List BrauerAtom) : Nat :=
  atomsRightOfFirstCup word * radix + straddleBitAtFirstCup word

/-! ## B — the tie-break digit is `≤ 1`, and the two lex→`Nat` combine lemmas -/

/-- The straddle window bit is `0` or `1`, so it is `≤ 1`. -/
theorem straddleWindowBit_le_one (first second : BrauerAtom) : straddleWindowBit first second ≤ 1 := by
  show cond (isCupAtom first && isCrossingAtom second && Nat.beq second.position (first.position + 1)) 1 0 ≤ 1
  cases (isCupAtom first && isCrossingAtom second && Nat.beq second.position (first.position + 1)) <;> decide

/-- ★ **The leftmost-cup straddle tie-break is `≤ 1`** — structural on the word, each arm is a window bit (`≤ 1`) or
the recursive tail (`≤ 1` by the induction).  Below any radix `> 1`, this is the secBound the primary combine lemma
needs, discharged generically. -/
theorem straddleBitAtFirstCup_le_one : (word : List BrauerAtom) → straddleBitAtFirstCup word ≤ 1
  | [] => Nat.zero_le 1
  | [_] => Nat.zero_le 1
  | first :: second :: rest => by
      show cond (isCupAtom first) (straddleWindowBit first second) (straddleBitAtFirstCup (second :: rest)) ≤ 1
      cases isCupAtom first with
      | true => exact straddleWindowBit_le_one first second
      | false => exact straddleBitAtFirstCup_le_one (second :: rest)

/-- Multiplication-free `(multiplier + 1) · radix = multiplier · radix + radix`. -/
private theorem succMulLeg (multiplier radix : Nat) :
    (multiplier + 1) * radix = multiplier * radix + radix := by
  rw [Nat.mul_comm (multiplier + 1) radix, Nat.mul_succ, Nat.mul_comm radix multiplier]

/-- ★ **Primary drop ⟹ `legLexFuel` drop** (given the tie-break of the after-word is below the radix).  Exact mirror
of the shipped `straddleLex_lt_of_primary`. -/
theorem legLex_lt_of_primary (radix : Nat) (wordAfter wordBefore : List BrauerAtom)
    (primLt : atomsRightOfFirstCup wordAfter < atomsRightOfFirstCup wordBefore)
    (secBound : straddleBitAtFirstCup wordAfter < radix) :
    legLexFuel radix wordAfter < legLexFuel radix wordBefore := by
  have blockLe : atomsRightOfFirstCup wordAfter * radix + radix
      ≤ atomsRightOfFirstCup wordBefore * radix := by
    rw [← succMulLeg]
    exact Nat.mul_le_mul_right radix primLt
  have belowBlock : atomsRightOfFirstCup wordAfter * radix + straddleBitAtFirstCup wordAfter
      < atomsRightOfFirstCup wordAfter * radix + radix :=
    Nat.add_lt_add_left secBound _
  show atomsRightOfFirstCup wordAfter * radix + straddleBitAtFirstCup wordAfter
     < atomsRightOfFirstCup wordBefore * radix + straddleBitAtFirstCup wordBefore
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le belowBlock blockLe) (Nat.le_add_right _ _)

/-- ★ **Primary held + tie-break drop ⟹ `legLexFuel` drop** (no radix bound needed).  Exact mirror of the shipped
`straddleLex_lt_of_secondary`. -/
theorem legLex_lt_of_secondary (radix : Nat) (wordAfter wordBefore : List BrauerAtom)
    (primEq : atomsRightOfFirstCup wordAfter = atomsRightOfFirstCup wordBefore)
    (secLt : straddleBitAtFirstCup wordAfter < straddleBitAtFirstCup wordBefore) :
    legLexFuel radix wordAfter < legLexFuel radix wordBefore := by
  show atomsRightOfFirstCup wordAfter * radix + straddleBitAtFirstCup wordAfter
     < atomsRightOfFirstCup wordBefore * radix + straddleBitAtFirstCup wordBefore
  rw [primEq]
  exact Nat.add_lt_add_left secLt _

/-! ## C — the leftmost-cup distance read-off in ARBITRARY cupless-prefix context (no `List.append_assoc`) -/

/-- A word contains no cup — the condition under which its atoms all sit to the LEFT of the leftmost cup of a larger
word.  Structural, propext-clean. -/
def hasNoCup : List BrauerAtom → Bool
  | [] => true
  | atom :: rest => cond (isCupAtom atom) false (hasNoCup rest)

/-- ★ **The leftmost-cup distance is the tail count, in arbitrary cupless-prefix context.**  When `prefixWord` has no
cup, `atomsRightOfFirstCup (prefixWord ++ (cupAt cupPos :: rest)) = countAtoms rest` — the prefix pushes the leftmost
cup right but does not change the count of atoms after it.  Standalone structural recursion on `prefixWord` (each
non-cup prefix atom is skipped by `atomsRightOfFirstCup`); NO `List.append_assoc`. -/
theorem atomsRightOfFirstCup_prefixCupless :
    (prefixWord : List BrauerAtom) → (cupPos : Nat) → (rest : List BrauerAtom) →
    hasNoCup prefixWord = true →
    atomsRightOfFirstCup (prefixWord ++ (cupAt cupPos :: rest)) = countAtoms rest
  | [], _, _, _ => rfl
  | atom :: restPrefix, cupPos, rest, cupless => by
      have expand : hasNoCup (atom :: restPrefix)
          = cond (isCupAtom atom) false (hasNoCup restPrefix) := rfl
      rw [expand] at cupless
      cases hAtom : isCupAtom atom with
      | true => rw [hAtom] at cupless; nomatch cupless
      | false =>
          rw [hAtom] at cupless
          show cond (isCupAtom atom) (countAtoms (restPrefix ++ (cupAt cupPos :: rest)))
                (atomsRightOfFirstCup (restPrefix ++ (cupAt cupPos :: rest))) = countAtoms rest
          rw [hAtom]
          exact atomsRightOfFirstCup_prefixCupless restPrefix cupPos rest cupless

/-- ★ **The leftmost-cup distance after a non-cup lands in front of the cup.**  When `prefixWord` has no cup and
`headAtom` is a non-cup, `atomsRightOfFirstCup (prefixWord ++ (headAtom :: cupAt cupPos :: rest)) = countAtoms rest` —
the leftmost cup now has ONE fewer atom after it (the non-cup that jumped past it left).  This is the "after" side of
every distant cup-sink cell.  Standalone recursion; NO `List.append_assoc`. -/
theorem atomsRightOfFirstCup_prefixCupless_nonCupThenCup :
    (prefixWord : List BrauerAtom) → (headAtom : BrauerAtom) → (cupPos : Nat) → (rest : List BrauerAtom) →
    hasNoCup prefixWord = true → isCupAtom headAtom = false →
    atomsRightOfFirstCup (prefixWord ++ (headAtom :: cupAt cupPos :: rest)) = countAtoms rest
  | [], headAtom, cupPos, rest, _, hHead => by
      show cond (isCupAtom headAtom) (countAtoms (cupAt cupPos :: rest))
            (atomsRightOfFirstCup (cupAt cupPos :: rest)) = countAtoms rest
      rw [hHead]
      exact atomsRightOfFirstCup_prefixCupless [] cupPos rest rfl
  | atom :: restPrefix, headAtom, cupPos, rest, cupless, hHead => by
      have expand : hasNoCup (atom :: restPrefix)
          = cond (isCupAtom atom) false (hasNoCup restPrefix) := rfl
      rw [expand] at cupless
      cases hAtom : isCupAtom atom with
      | true => rw [hAtom] at cupless; nomatch cupless
      | false =>
          rw [hAtom] at cupless
          show cond (isCupAtom atom) (countAtoms (restPrefix ++ (headAtom :: cupAt cupPos :: rest)))
                (atomsRightOfFirstCup (restPrefix ++ (headAtom :: cupAt cupPos :: rest))) = countAtoms rest
          rw [hAtom]
          exact atomsRightOfFirstCup_prefixCupless_nonCupThenCup restPrefix headAtom cupPos rest cupless hHead

/-! ## D — the PRIMARY (distance) descent of a distant cup-sink, whiskered into arbitrary context -/

/-- ★★ **The leg fuel descends when the leftmost cup sinks past a DISTANT crossing, in arbitrary context.**  For any
cupless prefix, any suffix, and radix `> 1`, `legLexFuel` strictly drops across the distant cup-past-crossing slide
`prefixWord ++ (cupAt cupPos :: crossingAt (crossPos + 2) :: suffixWord) ↝ prefixWord ++ (crossingAt crossPos ::
cupAt cupPos :: suffixWord)`: the leftmost-cup distance drops by one (`1 + countAtoms suffixWord ↝ countAtoms
suffixWord`), the tie-break sits below the radix.  The GENERAL mechanism — the local fuel descends wherever the
leftmost cup sinks past a non-cup, not just on the width-3 witness. -/
theorem legFuel_leftmostCupCrossing_lt (radix cupPos crossPos : Nat)
    (prefixWord suffixWord : List BrauerAtom)
    (cupless : hasNoCup prefixWord = true) (radixBig : 1 < radix) :
    legLexFuel radix (prefixWord ++ (crossingAt crossPos :: cupAt cupPos :: suffixWord))
      < legLexFuel radix (prefixWord ++ (cupAt cupPos :: crossingAt (crossPos + 2) :: suffixWord)) := by
  apply legLex_lt_of_primary
  · rw [atomsRightOfFirstCup_prefixCupless_nonCupThenCup prefixWord (crossingAt crossPos) cupPos suffixWord
          cupless rfl,
        atomsRightOfFirstCup_prefixCupless prefixWord cupPos (crossingAt (crossPos + 2) :: suffixWord) cupless]
    show countAtoms suffixWord < 1 + countAtoms suffixWord
    rw [Nat.add_comm 1 (countAtoms suffixWord)]
    exact Nat.lt_succ_self _
  · exact Nat.lt_of_le_of_lt (straddleBitAtFirstCup_le_one _) radixBig

/-- ★★ **The leg fuel descends when the leftmost cup sinks past a DISTANT cap, in arbitrary context.**  The ∗-mirror of
`legFuel_leftmostCupCrossing_lt` for the cup-past-cap slide `prefixWord ++ (cupAt cupPos :: capAt (capPos + 2) ::
suffixWord) ↝ prefixWord ++ (capAt capPos :: cupAt cupPos :: suffixWord)`. -/
theorem legFuel_leftmostCupCap_lt (radix cupPos capPos : Nat)
    (prefixWord suffixWord : List BrauerAtom)
    (cupless : hasNoCup prefixWord = true) (radixBig : 1 < radix) :
    legLexFuel radix (prefixWord ++ (capAt capPos :: cupAt cupPos :: suffixWord))
      < legLexFuel radix (prefixWord ++ (cupAt cupPos :: capAt (capPos + 2) :: suffixWord)) := by
  apply legLex_lt_of_primary
  · rw [atomsRightOfFirstCup_prefixCupless_nonCupThenCup prefixWord (capAt capPos) cupPos suffixWord
          cupless rfl,
        atomsRightOfFirstCup_prefixCupless prefixWord cupPos (capAt (capPos + 2) :: suffixWord) cupless]
    show countAtoms suffixWord < 1 + countAtoms suffixWord
    rw [Nat.add_comm 1 (countAtoms suffixWord)]
    exact Nat.lt_succ_self _
  · exact Nat.lt_of_le_of_lt (straddleBitAtFirstCup_le_one _) radixBig

/-! ## E — the flagship: the leg fuel crosses the exact chain that REFUTED the global measure -/

/-- ★★ **THE re-exposure chain, discharged by the LOCAL leg fuel.**  The three-word `BrauerConvFree8` reduction
`[cupAt 0, crossingAt 2, crossingAt 1] ↝ [crossingAt 0, cupAt 0, crossingAt 1] ↝ [crossingAt 0, cupAt 1, crossingAt 0]`
(two whisker-free cells: a distant cup-past-crossing slide, then the adjacent straddle relabel) is the EXACT chain the
r33 wall marker `fxBrauer_hasStraddleGlobalFuelBounded` refutes for the GLOBAL measure.  Here:

  * the LOCAL `legLexFuel 8` STRICTLY DESCENDS on BOTH cells — `16 > 9 > 8` (cell 1 via the PRIMARY distance
    `2 → 1`, cell 2 via the SECONDARY tie-break `1 → 0`);
  * the GLOBAL `straddleLexMeasure 16 8` ASCENDS on cell 1 — `16 < 24` — the primary re-exposure the global sum
    cannot see past.

So the local leg fuel performs the arc-level `recComb` chain that BOTH shipped fuels jam on (`arcMeasure` at the
straddle, `straddleLexMeasure` at the re-exposure), threading ONLY the free `BrauerConvFree8` constructors. -/
theorem legFuelFold_throughReexposure_demo :
    BrauerConvFree8 [cupAt 0, crossingAt 2, crossingAt 1] [crossingAt 0, cupAt 1, crossingAt 0]
      ∧ legLexFuel 8 [crossingAt 0, cupAt 0, crossingAt 1] < legLexFuel 8 [cupAt 0, crossingAt 2, crossingAt 1]
      ∧ legLexFuel 8 [crossingAt 0, cupAt 1, crossingAt 0] < legLexFuel 8 [crossingAt 0, cupAt 0, crossingAt 1]
      ∧ straddleLexMeasure 16 8 [cupAt 0, crossingAt 2, crossingAt 1]
          < straddleLexMeasure 16 8 [crossingAt 0, cupAt 0, crossingAt 1] := by
  refine ⟨?_, by decide, by decide, by decide⟩
  exact BrauerConvFree8.trans
    (BrauerConvFree8.whiskerRight [crossingAt 1] (distantCupCrossingSlideFree8 0 0 (by decide)))
    (BrauerConvFree8.whiskerLeft [crossingAt 0] (BrauerConvFree8.cupSlide 0))

/-- ★ **The three sinking cells each drop the leg fuel; the sibling cup/cup reorder holds the primary.**  Cell drops
(`legLexFuel 8`): cup/cap `8 → 0`, cup/crossing `8 → 0`, straddle `9 → 8`.  The sibling cup/cup reorder holds the
primary distance (both operands are cups — the leftmost stays leftmost), so it is NOT a leg-fuel cell: it is the
within-cup-block reorder, governed by the shipped `arcMeasure` secondary, not by the leftmost-cup distance. -/
theorem legFuel_perCell_drops :
    legLexFuel 8 [capAt 0, cupAt 0] < legLexFuel 8 [cupAt 0, capAt 2]
      ∧ legLexFuel 8 [crossingAt 0, cupAt 0] < legLexFuel 8 [cupAt 0, crossingAt 2]
      ∧ legLexFuel 8 [cupAt 1, crossingAt 0] < legLexFuel 8 [cupAt 0, crossingAt 1]
      ∧ atomsRightOfFirstCup [cupAt 0, cupAt 0] = atomsRightOfFirstCup [cupAt 0, cupAt 2] :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the LOCAL per-cup arc-insertion leg fuel DESCENDS where the GLOBAL measure was REFUTED.**
`legLexFuel` (leftmost-cup distance `atomsRightOfFirstCup` primary + its straddle window `straddleBitAtFirstCup`
tie-break) strictly DESCENDS on the exact re-exposure chain the r33 `fxBrauer_hasStraddleGlobalFuelBounded` wall
refutes for the global lex — `16 > 9 > 8` where `straddleLexMeasure` ASCENDS `16 → 24`
(`legFuelFold_throughReexposure_demo`) — carrying a real whisker-free `BrauerConvFree8` reduction.  Its PRIMARY
(distance) descent generalizes to arbitrary cupless-prefix + arbitrary-suffix context
(`legFuel_leftmostCupCrossing_lt` / `legFuel_leftmostCupCap_lt`), so it is a genuine mechanism, not a width-3
coincidence; the three sinking cells each drop it (`legFuel_perCell_drops`).  The ordering discipline r33 named is now
a measure.  `= true`. -/
def fxBrauer_hasLocalLegFuelDescent : Bool := true

/-- **Honesty WALL marker — the full INNER descent is NOT a discharged fold; #2013 does NOT close.**  The local leg
fuel is the buildable INNER measure and its primary descent is general, but the two-level assembly is unbuilt: (J1) the
OUTER `arcCountFuel` (`fxBrauer_hasStagedArcCountFuel = true`) threaded with this INNER leg fuel, peeling a completed
arc with placed arcs untouched; (J2) the cap-side ∗-dual sink; (J3) the `bottomCount = 0` all-cup/all-loop class; (J4)
the whisker-free driver consuming a `DiagramType` + the R3-A connectivity roundtrip its guard needs.  So
`fxBrauer_hasStagedInnerDescentDischarged` STAYS `false`, and `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`.  A route / measure gap, never
a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasLocalLegFuelGlobalFold : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r34 terminal state — MACHINE-CHECKED.**  The new ingredient marker is `true` (the local per-cup
leg fuel descends where the global measure was refuted, with a general primary descent), on top of the shipped
`fxBrauer_hasStagedArcCountFuel` (the OUTER arc-count fuel) and `fxBrauer_hasStraddleSinkUnconditional` (the
unconditional straddle rung), while the INNER descent discharge and all three completeness masters STAY `false`.  A
`rfl`-conjunction the kernel checks; this round is purely additive, no master flip is fabricated, #2013 does NOT
close. -/
theorem fxBrauer_localLegFuelTerminalState :
    fxBrauer_hasLocalLegFuelDescent = true
      ∧ fxBrauer_hasStagedArcCountFuel = true
      ∧ fxBrauer_hasStraddleSinkUnconditional = true
      ∧ fxBrauer_hasLocalLegFuelGlobalFold = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasStraddleGlobalFuel = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
