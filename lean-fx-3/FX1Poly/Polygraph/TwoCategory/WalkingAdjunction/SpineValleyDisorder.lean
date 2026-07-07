import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyProgress

/-! # mode-3 keystone — Piece I: the valley-descent DISORDER MEASURE + the terminating tag-level driver

Piece I of the `MatchingReductsShareSpineTrace` beam is the descent `cell ≈sat valleyNF(cell)`: iterate
"locate an adjacent cup-then-cap, straighten|commute it" until the spine is a pure `cap`-block-then-`cup`-block
VALLEY.  `SpineValleyProgress` shipped the locate brick (a non-valley spine HAS an adjacent cup-then-cap,
`hasAdjacentCupThenCap_of_not_valley_spine`) and `SpineValleyDescent` shipped the two per-move invariants
(`matchingOf` fixed, `generatorCount` drops).  Missing was the WELL-FOUNDED DRIVER — a single strictly-decreasing
measure covering BOTH moves (`generatorCount` stalls under a pure Godement COMMUTE), plus the terminating
iteration itself.

This file supplies that measure and CLOSES the descent AT THE PURE-TAG LEVEL:

  * ★ **the DISORDER measure** `spineDisorder` — the inversion count of the cup/cap-tagged spine (a `cup`
    scoring `1`, a `cap` scoring `0`, so a `cup`-before-`cap` is an INVERSION).  A valley (caps then cups) is
    exactly the sorted-ascending tag word, i.e. ZERO inversions; every straighten/commute step is a
    descending swap or an inversion deletion, both of which strictly drop the count.  A generic port of the
    audit-clean `OmegacE/SortingTermination` inversion machinery from `OmegacECell` to `{α} (slotValue)`.
  * ★ **the valley bridge** — `spineDisorder = 0 ↔ isCapThenCupValley` (both directions): a valley has zero
    disorder (`countInversions_zero_of_valley`), and zero disorder forces a valley
    (`valley_of_disorder_zero`, via the shipped progress lemma + "an adjacent cup-then-cap is an inversion").
  * ★ **the three tractable descent bricks** — `readbackSplit_exposesRedex` (a non-valley tag word exposes a
    concrete cup-then-cap redex whose slots are a genuine inversion), and the two strict-decrease facts
    `countInversions_swap_adjacent_lt` (COMMUTE) / `countInversions_delete_head_lt` (STRAIGHTEN).
  * ★ **the fuel-structural `valleyDescentDriver`** — locate the first adjacent cup-then-cap, swap it, recurse
    on decremented fuel; TERMINATION + VALLEY-CORRECTNESS proved (`valleyDescentDriver_reaches_valley`:
    disorder ≤ fuel ⟹ the result is a valley), so `spineValleyNormalize` (fuel := the initial disorder) ALWAYS
    returns a valley (`spineValleyNormalize_isValley`).  Structural recursion on the fuel `Nat`; NO
    `WellFounded.fix`.

## What this does NOT close (the remaining Piece I work — the cell-level lift; gates stay `false`)

The driver here permutes the pure cup/cap-TAG word.  Three inputs remain open before this descent produces a
`SaturatedTwoCellConv cellA (valleyNF cellA)` (Piece I proper):

  1. the **typed spine** — `SpineAtom` is a boundary-CHAINED list, not a plain `List`; each tag swap/delete must
     typecheck against the chained modes (`leftMidMode` / `rightMidMode` / `leftContext`), which the pure-tag
     idealization elides;
  2. the **spine-position → cell-subterm bridge** — the located `capPrefix ++ cup :: cap :: rest` split must be
     exhibited as a `vcomp`/whisker redex feeding the shipped `zigzagStraightensInVcompContext` (straighten) /
     `saturatedGodementExchange` (commute), lifting each tag step to a `SaturatedTwoCellConv` step;
  3. the **`reify` base case** — the terminal valley must equal `reify (matchingOf cell)`
     (`MatchingStaircaseReconstructs` / `fxMode_hasArcCellReconstruction = false`, refuted at the general
     signature).

So this file delivers the terminating WF descent argument the plan named — a complete tag-level normalizer with a
proven strictly-decreasing measure — but it does NOT flip the fib-3 gate flags: inhabiting
`MatchingReductsShareSpineTrace` needs this Piece I lifted to cells AND the parallel Piece II
(`ValleyMatchingSpineTraceEquiv` whole-valley split), and `convOfMapEq` stays gated.

Raw Lean 4 + Init; the measure is a `List`/`Nat` fold, the append homomorphism explicit `Nat.add_assoc` /
`Nat.add_left_comm` (no `omega`, no AC-`simp`), the driver structural on fuel.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## The generic inversion-count measure (ported from `OmegacE/SortingTermination`) -/

/-- Count the elements whose `slotValue` is strictly below a threshold. -/
def countBelowThreshold {α : Type u} (slotValue : α → Nat) (threshold : Nat) : List α → Nat
  | [] => 0
  | head :: tail =>
      (if slotValue head < threshold then 1 else 0) + countBelowThreshold slotValue threshold tail

/-- The inversion count: for each head, the number of later elements with strictly smaller `slotValue`, plus the
recursion.  Strictly decreased by every descending swap — the bubble-sort termination measure. -/
def countInversions {α : Type u} (slotValue : α → Nat) : List α → Nat
  | [] => 0
  | head :: tail =>
      countBelowThreshold slotValue (slotValue head) tail + countInversions slotValue tail

/-- The CROSS inversion count across an append boundary — each left element pairs with each strictly-smaller
right element.  The cross term of the inversion-count append homomorphism. -/
def crossInversionCount {α : Type u} (slotValue : α → Nat) : List α → List α → Nat
  | [], _ => 0
  | head :: tail, rightCells =>
      countBelowThreshold slotValue (slotValue head) rightCells
        + crossInversionCount slotValue tail rightCells

/-- Below a threshold of `0` nothing counts (no `Nat` is `< 0`) — the annihilator of the below-threshold count. -/
theorem countBelowThreshold_zero {α : Type u} (slotValue : α → Nat) (list : List α) :
    countBelowThreshold slotValue 0 list = 0 := by
  induction list with
  | nil => rfl
  | cons head tail ih =>
      show (if slotValue head < 0 then 1 else 0) + countBelowThreshold slotValue 0 tail = 0
      rw [if_neg (Nat.not_lt_zero (slotValue head)), Nat.zero_add, ih]

/-- `countBelowThreshold` is a monoid homomorphism from list append to `ℕ` addition. -/
theorem countBelowThreshold_append {α : Type u} (slotValue : α → Nat) (threshold : Nat)
    (leftCells rightCells : List α) :
    countBelowThreshold slotValue threshold (leftCells ++ rightCells)
      = countBelowThreshold slotValue threshold leftCells
        + countBelowThreshold slotValue threshold rightCells := by
  induction leftCells with
  | nil =>
      show countBelowThreshold slotValue threshold rightCells
        = 0 + countBelowThreshold slotValue threshold rightCells
      rw [Nat.zero_add]
  | cons head tail ih =>
      show (if slotValue head < threshold then 1 else 0)
          + countBelowThreshold slotValue threshold (tail ++ rightCells)
        = ((if slotValue head < threshold then 1 else 0)
            + countBelowThreshold slotValue threshold tail)
          + countBelowThreshold slotValue threshold rightCells
      rw [ih, Nat.add_assoc]

/-- **Inversion count over an append**: the inversions of `left ++ right` are the inversions within `left`, plus
those within `right`, plus the CROSS inversions.  The structural law behind the redex-positivity argument. -/
theorem countInversions_append {α : Type u} (slotValue : α → Nat) (leftCells rightCells : List α) :
    countInversions slotValue (leftCells ++ rightCells)
      = countInversions slotValue leftCells + countInversions slotValue rightCells
        + crossInversionCount slotValue leftCells rightCells := by
  induction leftCells with
  | nil =>
      show countInversions slotValue rightCells = 0 + countInversions slotValue rightCells + 0
      rw [Nat.zero_add, Nat.add_zero]
  | cons head tail ih =>
      show countBelowThreshold slotValue (slotValue head) (tail ++ rightCells)
          + countInversions slotValue (tail ++ rightCells)
        = (countBelowThreshold slotValue (slotValue head) tail + countInversions slotValue tail)
          + countInversions slotValue rightCells
          + (countBelowThreshold slotValue (slotValue head) rightCells
              + crossInversionCount slotValue tail rightCells)
      rw [countBelowThreshold_append, ih]
      generalize countBelowThreshold slotValue (slotValue head) tail = headBelowLeft
      generalize countBelowThreshold slotValue (slotValue head) rightCells = headBelowRight
      generalize countInversions slotValue tail = invLeft
      generalize countInversions slotValue rightCells = invRight
      generalize crossInversionCount slotValue tail rightCells = crossTerm
      rw [Nat.add_assoc headBelowLeft headBelowRight ((invLeft + invRight) + crossTerm),
          Nat.add_assoc invLeft invRight crossTerm,
          Nat.add_assoc (headBelowLeft + invLeft) invRight (headBelowRight + crossTerm),
          Nat.add_assoc headBelowLeft invLeft (invRight + (headBelowRight + crossTerm)),
          Nat.add_left_comm headBelowRight invLeft (invRight + crossTerm),
          Nat.add_left_comm headBelowRight invRight crossTerm]

/-! ## Adjacent-swap arithmetic (the COMMUTE and STRAIGHTEN strict-decrease facts) -/

/-- The below-threshold count is invariant under swapping two adjacent elements (the multiset is preserved). -/
theorem countBelowThreshold_swap_adjacent {α : Type u} (slotValue : α → Nat) (threshold : Nat)
    (firstCell secondCell : α) (rest : List α) :
    countBelowThreshold slotValue threshold (firstCell :: secondCell :: rest)
      = countBelowThreshold slotValue threshold (secondCell :: firstCell :: rest) := by
  show (if slotValue firstCell < threshold then 1 else 0)
        + ((if slotValue secondCell < threshold then 1 else 0)
            + countBelowThreshold slotValue threshold rest)
    = (if slotValue secondCell < threshold then 1 else 0)
        + ((if slotValue firstCell < threshold then 1 else 0)
            + countBelowThreshold slotValue threshold rest)
  generalize (if slotValue firstCell < threshold then (1 : Nat) else 0) = indicatorFirst
  generalize (if slotValue secondCell < threshold then (1 : Nat) else 0) = indicatorSecond
  generalize countBelowThreshold slotValue threshold rest = restCount
  exact Nat.add_left_comm indicatorFirst indicatorSecond restCount

/-- **The COMMUTE step drops disorder by exactly one.**  Swapping an adjacent descending pair `a :: b`
(`slotValue b < slotValue a`) to `b :: a` removes precisely the `a`-`b` inversion.  The equality behind the pure
Godement commute's strict decrease. -/
theorem countInversions_swap_adjacent_eq {α : Type u} (slotValue : α → Nat) {biggerCell smallerCell : α}
    (descending : slotValue smallerCell < slotValue biggerCell) (rest : List α) :
    countInversions slotValue (biggerCell :: smallerCell :: rest)
      = countInversions slotValue (smallerCell :: biggerCell :: rest) + 1 := by
  show ((if slotValue smallerCell < slotValue biggerCell then 1 else 0)
        + countBelowThreshold slotValue (slotValue biggerCell) rest)
      + (countBelowThreshold slotValue (slotValue smallerCell) rest + countInversions slotValue rest)
    = (((if slotValue biggerCell < slotValue smallerCell then 1 else 0)
          + countBelowThreshold slotValue (slotValue smallerCell) rest)
        + (countBelowThreshold slotValue (slotValue biggerCell) rest + countInversions slotValue rest)) + 1
  rw [if_pos descending, if_neg (Nat.lt_asymm descending)]
  generalize countBelowThreshold slotValue (slotValue biggerCell) rest = countBigger
  generalize countBelowThreshold slotValue (slotValue smallerCell) rest = countSmaller
  generalize countInversions slotValue rest = invRest
  show (1 + countBigger) + (countSmaller + invRest)
    = ((0 + countSmaller) + (countBigger + invRest)) + 1
  rw [Nat.zero_add, Nat.add_assoc 1 countBigger (countSmaller + invRest),
      Nat.add_left_comm countBigger countSmaller invRest,
      Nat.add_comm 1 (countSmaller + (countBigger + invRest))]

/-- **The COMMUTE step strictly decreases disorder** — the commuted word has one fewer inversion. -/
theorem countInversions_swap_adjacent_lt {α : Type u} (slotValue : α → Nat) {biggerCell smallerCell : α}
    (descending : slotValue smallerCell < slotValue biggerCell) (rest : List α) :
    countInversions slotValue (smallerCell :: biggerCell :: rest)
      < countInversions slotValue (biggerCell :: smallerCell :: rest) := by
  rw [countInversions_swap_adjacent_eq slotValue descending rest]
  exact Nat.lt_succ_self _

/-- **The STRAIGHTEN step strictly decreases disorder** — deleting an adjacent descending pair `a :: b`
(`slotValue b < slotValue a`, a genuine inversion) drops the inversion count.  The pure-tag form of the
zig-zag straighten (which removes the collapsed snake's two generators). -/
theorem countInversions_delete_head_lt {α : Type u} (slotValue : α → Nat) {biggerCell smallerCell : α}
    (descending : slotValue smallerCell < slotValue biggerCell) (rest : List α) :
    countInversions slotValue rest < countInversions slotValue (biggerCell :: smallerCell :: rest) := by
  have oneLeBelow :
      1 ≤ countBelowThreshold slotValue (slotValue biggerCell) (smallerCell :: rest) := by
    show 1 ≤ (if slotValue smallerCell < slotValue biggerCell then 1 else 0)
              + countBelowThreshold slotValue (slotValue biggerCell) rest
    rw [if_pos descending]
    exact Nat.le_add_right 1 _
  have restLeInner :
      countInversions slotValue rest ≤ countInversions slotValue (smallerCell :: rest) := by
    show countInversions slotValue rest
      ≤ countBelowThreshold slotValue (slotValue smallerCell) rest + countInversions slotValue rest
    exact Nat.le_add_left _ _
  show countInversions slotValue rest
    < countBelowThreshold slotValue (slotValue biggerCell) (smallerCell :: rest)
        + countInversions slotValue (smallerCell :: rest)
  refine Nat.lt_of_lt_of_le ?_ (Nat.add_le_add oneLeBelow restLeInner)
  rw [Nat.add_comm 1 (countInversions slotValue rest)]
  exact Nat.lt_succ_self _

/-! ## The cup/cap slot + the disorder of a spine -/

/-- The slot value of a cup/cap-tagged element: a `cup` scores `1`, a `cap` scores `0` — so a `cup`-before-`cap`
is an inversion, and the valley (caps then cups) is the sorted-ascending word with zero inversions. -/
def cupCapSlotValue {α : Type u} (isCup : α → Bool) (atom : α) : Nat := if isCup atom then 1 else 0

/-- A cup slots to `1`. -/
theorem cupCapSlotValue_cup {α : Type u} (isCup : α → Bool) {atom : α} (isCupAtom : isCup atom = true) :
    cupCapSlotValue isCup atom = 1 := if_pos isCupAtom

/-- A cap slots to `0`. -/
theorem cupCapSlotValue_cap {α : Type u} (isCup : α → Bool) {atom : α} (isCapAtom : isCup atom = false) :
    cupCapSlotValue isCup atom = 0 :=
  if_neg (by rw [isCapAtom]; exact fun equalTrue => Bool.noConfusion equalTrue)

/-- A cap slots strictly below a cup — an adjacent cup-then-cap is a genuine inversion. -/
theorem cupCapSlotValue_cap_lt_cup {α : Type u} (isCup : α → Bool) {capAtom cupAtom : α}
    (isCapAtom : isCup capAtom = false) (isCupAtom : isCup cupAtom = true) :
    cupCapSlotValue isCup capAtom < cupCapSlotValue isCup cupAtom := by
  rw [cupCapSlotValue_cap isCup isCapAtom, cupCapSlotValue_cup isCup isCupAtom]
  exact Nat.zero_lt_one

/-- **The DISORDER of a spine** — the inversion count of its cup/cap tags.  Zero iff the spine is a valley. -/
def spineDisorder {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (spine : List (SpineAtom signature sourceMode targetMode)) : Nat :=
  countInversions (cupCapSlotValue SpineAtom.isCupAtom) spine

/-! ## The valley bridge: `spineDisorder = 0 ↔ isCapThenCupValley` -/

/-- In an all-cups tail every slot is `1`, so nothing counts below threshold `1`. -/
theorem countBelowThreshold_one_of_allCups {α : Type u} (isCup : α → Bool) :
    ∀ {list : List α}, allCups isCup list = true →
      countBelowThreshold (cupCapSlotValue isCup) 1 list = 0
  | [], _ => rfl
  | head :: tail, allc => by
      dsimp only [allCups] at allc
      cases hHead : isCup head with
      | false => rw [hHead, Bool.false_and] at allc; exact Bool.noConfusion allc
      | true =>
          rw [hHead, Bool.true_and] at allc
          show (if cupCapSlotValue isCup head < 1 then 1 else 0)
                + countBelowThreshold (cupCapSlotValue isCup) 1 tail = 0
          rw [cupCapSlotValue_cup isCup hHead, if_neg (Nat.lt_irrefl 1), Nat.zero_add,
              countBelowThreshold_one_of_allCups isCup allc]

/-- An all-cups word has zero inversions (all slots equal). -/
theorem countInversions_zero_of_allCups {α : Type u} (isCup : α → Bool) :
    ∀ {list : List α}, allCups isCup list = true → countInversions (cupCapSlotValue isCup) list = 0
  | [], _ => rfl
  | head :: tail, allc => by
      dsimp only [allCups] at allc
      cases hHead : isCup head with
      | false => rw [hHead, Bool.false_and] at allc; exact Bool.noConfusion allc
      | true =>
          rw [hHead, Bool.true_and] at allc
          show countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup head) tail
                + countInversions (cupCapSlotValue isCup) tail = 0
          rw [cupCapSlotValue_cup isCup hHead, countBelowThreshold_one_of_allCups isCup allc,
              countInversions_zero_of_allCups isCup allc, Nat.zero_add]

/-- **A valley has zero disorder** — the forward direction of the bridge.  A `cap`-block-then-`cup`-block word
has no cup-before-cap, hence no inversion.  (Caps score `0` — nothing below threshold `0`; the leading cup, once
reached, is followed only by cups — nothing below threshold `1`.) -/
theorem countInversions_zero_of_valley {α : Type u} (isCup : α → Bool) :
    ∀ {list : List α}, isCapThenCupValley isCup list = true →
      countInversions (cupCapSlotValue isCup) list = 0
  | [], _ => rfl
  | head :: tail, hval => by
      dsimp only [isCapThenCupValley] at hval
      cases hHead : isCup head with
      | true =>
          rw [hHead] at hval
          show countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup head) tail
                + countInversions (cupCapSlotValue isCup) tail = 0
          rw [cupCapSlotValue_cup isCup hHead, countBelowThreshold_one_of_allCups isCup hval,
              countInversions_zero_of_allCups isCup hval, Nat.zero_add]
      | false =>
          rw [hHead] at hval
          show countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup head) tail
                + countInversions (cupCapSlotValue isCup) tail = 0
          rw [cupCapSlotValue_cap isCup hHead, countBelowThreshold_zero, Nat.zero_add]
          exact countInversions_zero_of_valley isCup hval

/-- **A non-valley word has positive disorder** — an adjacent cup-then-cap is a genuine inversion
(`cup` scores `1`, the following `cap` scores `0 < 1`), contributing at least one to the inversion count. -/
theorem countInversions_pos_of_hasAdjacent {α : Type u} (isCup : α → Bool) {list : List α}
    (redex : HasAdjacentCupThenCap isCup list) :
    0 < countInversions (cupCapSlotValue isCup) list := by
  obtain ⟨capPrefix, cupAtom, capAtom, suffixRest, splitEq, isCupCup, isCapCap⟩ :=
    hasAdjacentCupThenCap_split isCup redex
  subst splitEq
  rw [countInversions_append]
  have oneLeInner : 1 ≤ countInversions (cupCapSlotValue isCup) (cupAtom :: capAtom :: suffixRest) := by
    show 1 ≤ countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup cupAtom)
              (capAtom :: suffixRest)
            + countInversions (cupCapSlotValue isCup) (capAtom :: suffixRest)
    refine Nat.le_trans ?_ (Nat.le_add_right _ _)
    show 1 ≤ (if cupCapSlotValue isCup capAtom < cupCapSlotValue isCup cupAtom then 1 else 0)
              + countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup cupAtom) suffixRest
    rw [if_pos (cupCapSlotValue_cap_lt_cup isCup isCapCap isCupCup)]
    exact Nat.le_add_right 1 _
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one oneLeInner)
    (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))

/-- **Zero disorder forces a valley** — the reverse direction of the bridge.  Contrapositive of the progress
lemma: a non-valley word has an adjacent cup-then-cap, which is an inversion, so nonzero disorder. -/
theorem valley_of_disorder_zero {α : Type u} (isCup : α → Bool) {list : List α}
    (disorderZero : countInversions (cupCapSlotValue isCup) list = 0) :
    isCapThenCupValley isCup list = true := by
  cases hval : isCapThenCupValley isCup list with
  | true => rfl
  | false =>
      have positive :=
        countInversions_pos_of_hasAdjacent isCup (hasAdjacentCupThenCap_of_not_valley isCup hval)
      rw [disorderZero] at positive
      exact absurd positive (Nat.lt_irrefl 0)

/-! ## Descent brick — a non-valley word EXPOSES a redex -/

/-- ★ **`readbackSplit_exposesRedex`** — the descent's locate brick with the inversion tag attached.  A word that
is not a `cap`-block-then-`cup`-block valley splits concretely as `capPrefix ++ cupAtom :: capAtom :: suffixRest`
with `cupAtom` a cup, `capAtom` a cap, and their slots a genuine inversion (`slot capAtom < slot cupAtom`) — the
redex the straighten/commute step consumes.  Wraps the shipped `hasAdjacentCupThenCap_of_not_valley` +
`hasAdjacentCupThenCap_split`; no arc/window readoff. -/
theorem readbackSplit_exposesRedex {α : Type u} (isCup : α → Bool) {tags : List α}
    (notValley : isCapThenCupValley isCup tags = false) :
    ∃ (capPrefix : List α) (cupAtom capAtom : α) (suffixRest : List α),
      tags = capPrefix ++ cupAtom :: capAtom :: suffixRest ∧
        isCup cupAtom = true ∧ isCup capAtom = false ∧
        cupCapSlotValue isCup capAtom < cupCapSlotValue isCup cupAtom := by
  obtain ⟨capPrefix, cupAtom, capAtom, suffixRest, splitEq, isCupCup, isCapCap⟩ :=
    hasAdjacentCupThenCap_split isCup (hasAdjacentCupThenCap_of_not_valley isCup notValley)
  exact ⟨capPrefix, cupAtom, capAtom, suffixRest, splitEq, isCupCup, isCapCap,
    cupCapSlotValue_cap_lt_cup isCup isCapCap isCupCup⟩

/-! ## The single descent move on the tag word: swap the first adjacent cup-then-cap -/

/-- **The descent MOVE (commute presentation)** — swap the first adjacent cup-then-cap of the tag word.  A pure
structural pass: at the first position where a cup is immediately followed by a cap, transpose them; otherwise
peel the head and recurse.  Bubble-sorts the tags toward the caps-then-cups valley. -/
def swapFirstCupCap {α : Type u} (isCup : α → Bool) : List α → List α
  | [] => []
  | [single] => [single]
  | firstCell :: secondCell :: rest =>
      bif isCup firstCell && !isCup secondCell then secondCell :: firstCell :: rest
      else firstCell :: swapFirstCupCap isCup (secondCell :: rest)

/-- The swap pass preserves the below-threshold count (it only transposes two adjacent elements). -/
theorem countBelowThreshold_swapFirstCupCap {α : Type u} (isCup : α → Bool) (slotValue : α → Nat)
    (threshold : Nat) :
    ∀ tags : List α,
      countBelowThreshold slotValue threshold (swapFirstCupCap isCup tags)
        = countBelowThreshold slotValue threshold tags
  | [] => rfl
  | [_single] => rfl
  | firstCell :: secondCell :: rest => by
      dsimp only [swapFirstCupCap]
      cases hcond : isCup firstCell && !isCup secondCell with
      | true =>
          exact countBelowThreshold_swap_adjacent slotValue threshold secondCell firstCell rest
      | false =>
          show (if slotValue firstCell < threshold then 1 else 0)
                + countBelowThreshold slotValue threshold (swapFirstCupCap isCup (secondCell :: rest))
            = (if slotValue firstCell < threshold then 1 else 0)
                + countBelowThreshold slotValue threshold (secondCell :: rest)
          rw [countBelowThreshold_swapFirstCupCap isCup slotValue threshold (secondCell :: rest)]

/-- One-step unfolding of the valley predicate on a two-or-more word (definitional; folds the tail call). -/
theorem isCapThenCupValley_cons_cons {α : Type u} (isCup : α → Bool) (firstCell secondCell : α)
    (rest : List α) :
    isCapThenCupValley isCup (firstCell :: secondCell :: rest)
      = (match isCup firstCell with
         | true => allCups isCup (secondCell :: rest)
         | false => isCapThenCupValley isCup (secondCell :: rest)) := rfl

/-- ★ **The descent move strictly decreases disorder** — as long as the word is not yet a valley, swapping its
first adjacent cup-then-cap drops the inversion count.  The single strictly-decreasing measure covering the
descent (both the head swap and the recursed context step drop it).  The well-foundedness of the driver. -/
theorem swapFirstCupCap_disorder_lt {α : Type u} (isCup : α → Bool) :
    ∀ {tags : List α}, isCapThenCupValley isCup tags = false →
      countInversions (cupCapSlotValue isCup) (swapFirstCupCap isCup tags)
        < countInversions (cupCapSlotValue isCup) tags
  | [], notValley => by
      dsimp only [isCapThenCupValley] at notValley
      exact Bool.noConfusion notValley
  | [single], notValley => by
      dsimp only [isCapThenCupValley] at notValley
      cases hHead : isCup single with
      | true => rw [hHead] at notValley; exact Bool.noConfusion notValley
      | false => rw [hHead] at notValley; exact Bool.noConfusion notValley
  | firstCell :: secondCell :: rest, notValley => by
      rw [isCapThenCupValley_cons_cons] at notValley
      dsimp only [swapFirstCupCap]
      cases hFirst : isCup firstCell with
      | true =>
          rw [hFirst] at notValley
          dsimp only [allCups] at notValley
          cases hSecond : isCup secondCell with
          | false =>
              exact countInversions_swap_adjacent_lt (cupCapSlotValue isCup)
                (cupCapSlotValue_cap_lt_cup isCup hSecond hFirst) rest
          | true =>
              rw [hSecond, Bool.true_and] at notValley
              have notValleyTail : isCapThenCupValley isCup (secondCell :: rest) = false := by
                dsimp only [isCapThenCupValley]; rw [hSecond]; exact notValley
              show countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup firstCell)
                    (swapFirstCupCap isCup (secondCell :: rest))
                  + countInversions (cupCapSlotValue isCup) (swapFirstCupCap isCup (secondCell :: rest))
                < countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup firstCell)
                    (secondCell :: rest)
                  + countInversions (cupCapSlotValue isCup) (secondCell :: rest)
              rw [countBelowThreshold_swapFirstCupCap isCup (cupCapSlotValue isCup)
                    (cupCapSlotValue isCup firstCell) (secondCell :: rest)]
              exact Nat.add_lt_add_left (swapFirstCupCap_disorder_lt isCup notValleyTail) _
      | false =>
          rw [hFirst] at notValley
          show countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup firstCell)
                (swapFirstCupCap isCup (secondCell :: rest))
              + countInversions (cupCapSlotValue isCup) (swapFirstCupCap isCup (secondCell :: rest))
            < countBelowThreshold (cupCapSlotValue isCup) (cupCapSlotValue isCup firstCell)
                (secondCell :: rest)
              + countInversions (cupCapSlotValue isCup) (secondCell :: rest)
          rw [countBelowThreshold_swapFirstCupCap isCup (cupCapSlotValue isCup)
                (cupCapSlotValue isCup firstCell) (secondCell :: rest)]
          exact Nat.add_lt_add_left (swapFirstCupCap_disorder_lt isCup notValley) _

/-! ## The fuel-structural driver + its termination / valley-correctness -/

/-- ★ **The valley-descent driver (fuel-structural).**  While the tag word is not a valley, swap its first
adjacent cup-then-cap and recurse on decremented fuel; a valley (or exhausted fuel) is returned as-is.  NO
`WellFounded.fix` — structural recursion on the fuel `Nat`; the fuel budget is discharged as sufficient by
`valleyDescentDriver_reaches_valley`. -/
def valleyDescentDriver {α : Type u} (isCup : α → Bool) : Nat → List α → List α
  | 0, tags => tags
  | fuel + 1, tags =>
      match isCapThenCupValley isCup tags with
      | true => tags
      | false => valleyDescentDriver isCup fuel (swapFirstCupCap isCup tags)

/-- ★ **Termination + valley-correctness of the driver.**  Given fuel at least the initial disorder, the driver
returns a VALLEY.  Structural induction on fuel: at zero, disorder ≤ 0 forces a valley already; at a successor,
either the word is a valley (returned) or the swap drops the disorder below the remaining fuel (the inductive
step).  The fuel budget = initial disorder is thereby proven sufficient. -/
theorem valleyDescentDriver_reaches_valley {α : Type u} (isCup : α → Bool) :
    ∀ (fuel : Nat) (tags : List α), countInversions (cupCapSlotValue isCup) tags ≤ fuel →
      isCapThenCupValley isCup (valleyDescentDriver isCup fuel tags) = true
  | 0, tags, disorderLe => by
      show isCapThenCupValley isCup tags = true
      exact valley_of_disorder_zero isCup (Nat.le_antisymm disorderLe (Nat.zero_le _))
  | fuel + 1, tags, disorderLe => by
      dsimp only [valleyDescentDriver]
      cases hval : isCapThenCupValley isCup tags with
      | true => exact hval
      | false =>
          have swapDrops := swapFirstCupCap_disorder_lt isCup hval
          have swapLe : countInversions (cupCapSlotValue isCup) (swapFirstCupCap isCup tags) ≤ fuel :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le swapDrops disorderLe)
          exact valleyDescentDriver_reaches_valley isCup fuel (swapFirstCupCap isCup tags) swapLe

/-- **Normalize a spine to a valley** — run the driver with fuel equal to the spine's disorder. -/
def spineValleyNormalize {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (spine : List (SpineAtom signature sourceMode targetMode)) :
    List (SpineAtom signature sourceMode targetMode) :=
  valleyDescentDriver SpineAtom.isCupAtom (spineDisorder spine) spine

/-- ★ **`spineValleyNormalize` always returns a valley** — the descent's tag-level total-correctness capstone.
The initial disorder is a sufficient fuel budget (`valleyDescentDriver_reaches_valley` at `disorder ≤ disorder`),
so the normalizer terminates AT a `cap`-block-then-`cup`-block valley. -/
theorem spineValleyNormalize_isValley {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (spine : List (SpineAtom signature sourceMode targetMode)) :
    isCapThenCupValley SpineAtom.isCupAtom (spineValleyNormalize spine) = true :=
  valleyDescentDriver_reaches_valley SpineAtom.isCupAtom (spineDisorder spine) spine (Nat.le_refl _)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — Piece I of the `MatchingReductsShareSpineTrace` beam is CLOSED AT THE PURE-TAG LEVEL.**
The disorder measure `spineDisorder` (inversion count of the cup/cap tags) is a genuine strictly-decreasing
descent measure: it is zero exactly on valleys (`countInversions_zero_of_valley` +
`valley_of_disorder_zero`), a non-valley word exposes an inversion redex (`readbackSplit_exposesRedex`), and both
the COMMUTE (`countInversions_swap_adjacent_lt`) and STRAIGHTEN (`countInversions_delete_head_lt`) moves strictly
drop it.  The fuel-structural `valleyDescentDriver` (no `WellFounded.fix`) is proven TERMINATING and
VALLEY-CORRECT (`valleyDescentDriver_reaches_valley`), so `spineValleyNormalize` always returns a valley
(`spineValleyNormalize_isValley`) — the terminating WF descent argument the plan named, complete at the tag layer.

  What this marker does NOT claim — the remaining Piece I work (the cell-level lift):
  * the **typed spine** — the swap must typecheck against `SpineAtom`'s boundary-chained modes, not a plain
    `List`;
  * the **spine-position → cell-subterm bridge** — each tag step must lift to a `SaturatedTwoCellConv` step via
    the shipped `zigzagStraightensInVcompContext` / `saturatedGodementExchange` on the located split;
  * the **`reify` base case** — the terminal valley must equal `reify (matchingOf cell)`
    (`fxMode_hasArcCellReconstruction = false`, refuted at the general signature).

  Also NOT closed here: the `orientationExcludedBothLegs` case-impossibility (the pure-swap tag driver never
  needs it — it is only required by the cell-level CLASSIFIED dispatch), and the flat-`SpineBoundaryChained` →
  `RealizedSpineChain` bridge at bare `TwoCellConv` (the totality is dodged by the shipped `RealizedSpineChain` /
  `chainToCell`; the flat→realized conversion exists only one level up at `TwoCellConvFull`).

  So inhabiting `MatchingReductsShareSpineTrace` needs this Piece I lifted to cells AND the parallel Piece II
  (whole-valley matching split); `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyDisorderDriver : Bool := true

end FX1Poly.Polygraph
