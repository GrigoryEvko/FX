import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # MatchingFreshUnshift — the two-zone shift's inverse on the punctured range

The downshift inverting `freshShiftAbove` off the consumed window pair: below the
threshold it is the identity, at or past it subtracts the delta.  On values avoiding
`{threshold, threshold + 1}` the delta-2 shift and unshift are mutually inverse, and the
unshift maps the padded range `[0, total + 2)` (punctured at the window pair) into
`[0, total)` — the index conversion every fused-entry closed form needs to express a
FRESH partner as a COMPOSITE index.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The downshift and its equations -/

/-- The two-zone downshift: identity below the threshold, subtract `delta` at or past it. -/
def freshUnshiftAbove (threshold delta value : Nat) : Nat :=
  if threshold ≤ value then value - delta else value

/-- The at-or-past-zone equation. -/
theorem freshUnshiftAbove_ofLe (threshold delta value : Nat)
    (thresholdLe : threshold ≤ value) :
    freshUnshiftAbove threshold delta value = value - delta :=
  if_pos thresholdLe

/-- The below-zone equation. -/
theorem freshUnshiftAbove_ofNotLe (threshold delta value : Nat)
    (thresholdNotLe : threshold ≤ value → False) :
    freshUnshiftAbove threshold delta value = value :=
  if_neg thresholdNotLe

/-! ## Private plumbing -/

/-- At or past the threshold but distinct from both window indices means at least two
past the threshold. -/
private theorem le_addTwo_ofNeWindowPair (threshold value : Nat)
    (windowLe : threshold ≤ value)
    (valueNeWindow : value ≠ threshold)
    (valueNeWindowSucc : value ≠ threshold + 1) :
    threshold + 2 ≤ value := by
  cases Nat.lt_or_ge value (threshold + 1) with
  | inl belowSucc =>
      exact False.elim (valueNeWindow
        (Nat.le_antisymm (Nat.le_of_lt_succ belowSucc) windowLe))
  | inr atLeastSucc =>
      cases Nat.lt_or_ge value (threshold + 2) with
      | inl belowTwo =>
          exact False.elim (valueNeWindowSucc
            (Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) atLeastSucc))
      | inr atLeastTwo => exact atLeastTwo

/-! ## The round trips -/

/-- **Unshift inverts shift everywhere**: the delta-2 downshift is a left inverse of the
delta-2 shift on every value. -/
theorem freshUnshiftAbove_ofShifted (threshold value : Nat) :
    freshUnshiftAbove threshold 2 (freshShiftAbove threshold 2 value) = value := by
  cases Nat.lt_or_ge value threshold with
  | inl below =>
      rw [freshShiftAbove_ofNotLe threshold 2 value
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe below))]
      exact freshUnshiftAbove_ofNotLe threshold 2 value
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe below))
  | inr atOrPast =>
      rw [freshShiftAbove_ofLe threshold 2 value atOrPast,
        freshUnshiftAbove_ofLe threshold 2 (value + 2)
          (Nat.le_trans atOrPast (Nat.le_add_right value 2))]
      rfl

/-- **Shift inverts unshift off the window pair**: on values distinct from both window
indices, the delta-2 shift is a left inverse of the delta-2 downshift. -/
theorem freshShiftAbove_ofUnshifted (threshold value : Nat)
    (valueNeWindow : value ≠ threshold)
    (valueNeWindowSucc : value ≠ threshold + 1) :
    freshShiftAbove threshold 2 (freshUnshiftAbove threshold 2 value) = value := by
  cases Nat.lt_or_ge value threshold with
  | inl below =>
      rw [freshUnshiftAbove_ofNotLe threshold 2 value
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe below))]
      exact freshShiftAbove_ofNotLe threshold 2 value
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe below))
  | inr atOrPast =>
      obtain ⟨pastOffset, pastSpec⟩ := Nat.le.dest
        (le_addTwo_ofNeWindowPair threshold value atOrPast valueNeWindow
          valueNeWindowSucc)
      rw [← pastSpec, Nat.add_right_comm threshold 2 pastOffset,
        freshUnshiftAbove_ofLe threshold 2 (threshold + pastOffset + 2)
          (Nat.le_trans (Nat.le_add_right threshold pastOffset)
            (Nat.le_add_right (threshold + pastOffset) 2))]
      show freshShiftAbove threshold 2 (threshold + pastOffset)
        = threshold + pastOffset + 2
      rw [freshShiftAbove_ofLe threshold 2 (threshold + pastOffset)
        (Nat.le_add_right threshold pastOffset)]

/-! ## The range bound -/

/-- **The unshift lands in the unpadded range**: a value below `total + 2`, distinct from
both window indices of a window fitting under `total`, downshifts below `total`. -/
theorem freshUnshiftAbove_ltTotal (threshold total value : Nat)
    (valueInPadded : value < total + 2)
    (valueNeWindow : value ≠ threshold)
    (valueNeWindowSucc : value ≠ threshold + 1)
    (windowLeTotal : threshold ≤ total) :
    freshUnshiftAbove threshold 2 value < total := by
  cases Nat.lt_or_ge value threshold with
  | inl below =>
      rw [freshUnshiftAbove_ofNotLe threshold 2 value
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe below))]
      exact Nat.lt_of_lt_of_le below windowLeTotal
  | inr atOrPast =>
      obtain ⟨pastOffset, pastSpec⟩ := Nat.le.dest
        (le_addTwo_ofNeWindowPair threshold value atOrPast valueNeWindow
          valueNeWindowSucc)
      have paddedLt : threshold + pastOffset + 2 < total + 2 := by
        rw [← Nat.add_right_comm threshold 2 pastOffset, pastSpec]
        exact valueInPadded
      rw [← pastSpec, Nat.add_right_comm threshold 2 pastOffset,
        freshUnshiftAbove_ofLe threshold 2 (threshold + pastOffset + 2)
          (Nat.le_trans (Nat.le_add_right threshold pastOffset)
            (Nat.le_add_right (threshold + pastOffset) 2))]
      show threshold + pastOffset < total
      exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ paddedLt)

/-- **Honesty marker — the two-zone downshift kit is SHIPPED (peel campaign H, cup rung
4).**  `freshUnshiftAbove` with its zone equations, both round trips
(`freshUnshiftAbove_ofShifted` everywhere, `freshShiftAbove_ofUnshifted` off the window
pair), and the punctured range bound (`freshUnshiftAbove_ltTotal`).  What this marker does
NOT claim: any fused-entry closed form riding the downshift.  `= true`. -/
def fxMode_hasMatchingFreshUnshift : Bool := true

end FX1Poly.Polygraph
