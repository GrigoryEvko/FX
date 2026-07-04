import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcWindowCommutation

/-! # ArcFreshBlockTransposition — the singleton swap's renaming sigma (ARC-2b brick iii-1b)

The two run orders of a disjoint-window swap allocate the SAME fresh identifiers in the
OPPOSITE order: run order 1 gives the first-fired atom the block
`[baseFresh, baseFresh + widthFirst)` and the second atom the adjacent block above it; run
order 2 hands the blocks out the other way round.  The renaming relating the two runs is
therefore the transposition of the two adjacent fresh blocks — identity below `baseFresh`
(where the whole pre-swap state lives, by `ArcStateFresh`), identity at or above
`baseFresh + widthFirst + widthSecond` (where the common suffix allocates), first block
shifted up by `widthSecond`, second block shifted down by `widthFirst`.

This file ships the sigma and its interface: the three fixing laws (below / zero / at-or-above
— exactly the `fixesBoundary` / `sigmaFixesZero` / `fixesAbove` premises of
`arcRenameRel_of_arcStepSimCount` and the `ArcStepSimCount` fold), the two block-value laws,
the left inverse (the transposition with swapped widths undoes it), and injectivity.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The fresh-block transposition.**  Identity below `baseFresh`; the first block
`[baseFresh, baseFresh + widthFirst)` moves up by `widthSecond`; the second block
`[baseFresh + widthFirst, baseFresh + widthFirst + widthSecond)` moves down by `widthFirst`;
identity at or above the blocks. -/
def arcFreshBlockTransposition (baseFresh widthFirst widthSecond identifier : Nat) : Nat :=
  if identifier < baseFresh then identifier
  else if identifier < baseFresh + widthFirst then identifier + widthSecond
  else if identifier < baseFresh + widthFirst + widthSecond then identifier - widthFirst
  else identifier

/-- No natural is strictly below a lower bound it dominates. -/
private theorem not_lt_of_le {lowerValue upperValue : Nat} (isAtLeast : lowerValue ≤ upperValue) :
    ¬ upperValue < lowerValue :=
  fun isBelow => absurd (Nat.lt_of_lt_of_le isBelow isAtLeast) (Nat.lt_irrefl upperValue)

/-- The transposition fixes every identifier strictly below the fresh base — in particular the
whole pre-swap state and the boundary range. -/
theorem arcFreshBlockTransposition_ofBelow
    (baseFresh widthFirst widthSecond identifier : Nat) (isBelow : identifier < baseFresh) :
    arcFreshBlockTransposition baseFresh widthFirst widthSecond identifier = identifier :=
  if_pos isBelow

/-- The transposition fixes `0` whenever the fresh base is positive — the scaffold's
`sigmaFixesZero` premise. -/
theorem arcFreshBlockTransposition_fixesZero
    (baseFresh widthFirst widthSecond : Nat) (isPositive : 0 < baseFresh) :
    arcFreshBlockTransposition baseFresh widthFirst widthSecond 0 = 0 :=
  arcFreshBlockTransposition_ofBelow baseFresh widthFirst widthSecond 0 isPositive

/-- The transposition fixes every identifier at or above both blocks — the scaffold's
`fixesAbove` premise for the common suffix. -/
theorem arcFreshBlockTransposition_ofAtOrAbove
    (baseFresh widthFirst widthSecond identifier : Nat)
    (isAtOrAbove : baseFresh + widthFirst + widthSecond ≤ identifier) :
    arcFreshBlockTransposition baseFresh widthFirst widthSecond identifier = identifier := by
  unfold arcFreshBlockTransposition
  rw [if_neg (not_lt_of_le (Nat.le_trans
        (Nat.le_trans (Nat.le_add_right baseFresh widthFirst)
          (Nat.le_add_right (baseFresh + widthFirst) widthSecond)) isAtOrAbove)),
    if_neg (not_lt_of_le (Nat.le_trans
        (Nat.le_add_right (baseFresh + widthFirst) widthSecond) isAtOrAbove)),
    if_neg (not_lt_of_le isAtOrAbove)]

/-- ★ **First-block value law**: an identifier in the first block moves up past the second
block's width. -/
theorem arcFreshBlockTransposition_onFirstBlock
    (baseFresh widthFirst widthSecond offset : Nat) (isInFirst : offset < widthFirst) :
    arcFreshBlockTransposition baseFresh widthFirst widthSecond (baseFresh + offset)
      = baseFresh + widthSecond + offset := by
  unfold arcFreshBlockTransposition
  rw [if_neg (not_lt_of_le (Nat.le_add_right baseFresh offset)),
    if_pos (Nat.add_lt_add_left isInFirst baseFresh),
    Nat.add_right_comm baseFresh offset widthSecond]

/-- Successor subtraction peels one successor from each side (hand-rolled — the core
`Nat.succ_sub_succ` / `Nat.add_sub_cancel` proofs are propext-tainted). -/
private theorem natSuccSubSucc :
    (minuend subtrahend : Nat) → Nat.succ minuend - Nat.succ subtrahend = minuend - subtrahend
  | _, 0 => rfl
  | minuend, subtrahend + 1 => by
      show Nat.pred (Nat.succ minuend - Nat.succ subtrahend) = minuend - (subtrahend + 1)
      rw [natSuccSubSucc minuend subtrahend]
      exact rfl

/-- Adding then subtracting a width cancels (hand-rolled propext-free replacement for
`Nat.add_sub_cancel`). -/
private theorem natAddSubCancel :
    (baseValue widthValue : Nat) → baseValue + widthValue - widthValue = baseValue
  | _, 0 => rfl
  | baseValue, widthValue + 1 => by
      show Nat.succ (baseValue + widthValue) - Nat.succ widthValue = baseValue
      rw [natSuccSubSucc (baseValue + widthValue) widthValue]
      exact natAddSubCancel baseValue widthValue

/-- ★ **Second-block value law**: an identifier in the second block moves down past the first
block's width. -/
theorem arcFreshBlockTransposition_onSecondBlock
    (baseFresh widthFirst widthSecond offset : Nat) (isInSecond : offset < widthSecond) :
    arcFreshBlockTransposition baseFresh widthFirst widthSecond (baseFresh + widthFirst + offset)
      = baseFresh + offset := by
  unfold arcFreshBlockTransposition
  rw [if_neg (not_lt_of_le (Nat.le_trans (Nat.le_add_right baseFresh widthFirst)
        (Nat.le_add_right (baseFresh + widthFirst) offset))),
    if_neg (not_lt_of_le (Nat.le_add_right (baseFresh + widthFirst) offset)),
    if_pos (Nat.add_lt_add_left isInSecond (baseFresh + widthFirst)),
    Nat.add_right_comm baseFresh widthFirst offset]
  exact natAddSubCancel (baseFresh + offset) widthFirst

/-- ★ **Left inverse**: the transposition with the widths swapped undoes the transposition —
the two blocks return to their places.  Case analysis on the four ranges, with each moved
identifier represented additively via `Nat.le.dest`. -/
theorem arcFreshBlockTransposition_leftInverse
    (baseFresh widthFirst widthSecond identifier : Nat) :
    arcFreshBlockTransposition baseFresh widthSecond widthFirst
        (arcFreshBlockTransposition baseFresh widthFirst widthSecond identifier)
      = identifier := by
  cases Nat.lt_or_ge identifier baseFresh with
  | inl isBelow =>
      rw [arcFreshBlockTransposition_ofBelow baseFresh widthFirst widthSecond identifier isBelow,
        arcFreshBlockTransposition_ofBelow baseFresh widthSecond widthFirst identifier isBelow]
  | inr isAtLeastBase =>
      cases Nat.lt_or_ge identifier (baseFresh + widthFirst) with
      | inl isInFirstRange =>
          obtain ⟨offset, offsetEquation⟩ := Nat.le.dest isAtLeastBase
          have offsetInFirst : offset < widthFirst := by
            apply Nat.lt_of_add_lt_add_left (n := baseFresh)
            rw [offsetEquation]
            exact isInFirstRange
          rw [← offsetEquation,
            arcFreshBlockTransposition_onFirstBlock baseFresh widthFirst widthSecond offset
              offsetInFirst,
            arcFreshBlockTransposition_onSecondBlock baseFresh widthSecond widthFirst offset
              offsetInFirst]
      | inr isAtLeastSecond =>
          cases Nat.lt_or_ge identifier (baseFresh + widthFirst + widthSecond) with
          | inl isInSecondRange =>
              obtain ⟨offset, offsetEquation⟩ := Nat.le.dest isAtLeastSecond
              have offsetInSecond : offset < widthSecond := by
                apply Nat.lt_of_add_lt_add_left (n := baseFresh + widthFirst)
                rw [offsetEquation]
                exact isInSecondRange
              rw [← offsetEquation,
                arcFreshBlockTransposition_onSecondBlock baseFresh widthFirst widthSecond offset
                  offsetInSecond,
                arcFreshBlockTransposition_onFirstBlock baseFresh widthSecond widthFirst offset
                  offsetInSecond]
          | inr isAtOrAboveAll =>
              have isAtOrAboveAllSwapped :
                  baseFresh + widthSecond + widthFirst ≤ identifier :=
                Nat.add_right_comm baseFresh widthFirst widthSecond ▸ isAtOrAboveAll
              rw [arcFreshBlockTransposition_ofAtOrAbove baseFresh widthFirst widthSecond
                  identifier isAtOrAboveAll,
                arcFreshBlockTransposition_ofAtOrAbove baseFresh widthSecond widthFirst
                  identifier isAtOrAboveAllSwapped]

/-- ★ **Injectivity** — the scaffold's `inj` premise, read off the left inverse. -/
theorem arcFreshBlockTransposition_injective
    (baseFresh widthFirst widthSecond firstId secondId : Nat)
    (imagesEqual : arcFreshBlockTransposition baseFresh widthFirst widthSecond firstId
      = arcFreshBlockTransposition baseFresh widthFirst widthSecond secondId) :
    firstId = secondId := by
  rw [← arcFreshBlockTransposition_leftInverse baseFresh widthFirst widthSecond firstId,
    ← arcFreshBlockTransposition_leftInverse baseFresh widthFirst widthSecond secondId,
    imagesEqual]

/-! ## Honesty marker -/

/-- **Honesty marker — the singleton swap's renaming sigma is SHIPPED (ARC-2b brick iii-1b).**
`arcFreshBlockTransposition` with its full `ArcStepSimCount`-facing interface: fixing laws
below / at zero / at-or-above (the `fixesBoundary` / `sigmaFixesZero` / `fixesAbove`
premises), the two block-value laws, the left inverse, and injectivity.  NOT yet shipped: the
two-step `ArcStepSimCount` core simulation over the realized swap pairs (consuming this sigma,
the iii-1a commutation kit, `stepArcAtom_congr`, and `ArcStateFresh`), and the arc-structure
equality along one bubble step read off through `arcRenameRel_of_arcStepSimCount` +
`sameArcPartition_of_renameRel` + `extractArc_eq_of_sameArcPartition`.  `= true`. -/
def fxMode_hasArcFreshBlockTransposition : Bool := true

end FX1Poly.Polygraph
