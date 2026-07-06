import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingMatching

/-! # NonCrossingBoundaryInvolution — the boundary linearization is a bijection on `[0, total)` (cup rung D2-prep)

The short-chord planar lemma (D2, `IsNonCrossing` ⟹ an innermost adjacent-matched pair exists) runs a
minimal-gap argument that needs `boundaryPosition bottomCount total` to be a BIJECTION on `[0, total)`:
"if the minimal arc has gap `> 1`, then `pos(a) + 1` is itself some boundary index's position" is exactly
surjectivity.  This brick establishes that, cheaply: `boundaryPosition bottomCount total` is its OWN
INVERSE on `[0, total)` — the bottom block `[0, bottomCount)` is fixed pointwise, and the top block
`[bottomCount, total)` is reversed (`bottomCount + (total-1-index)`), and reversing twice is the identity.
An involution on a set is a bijection, so `boundaryPosition` is injective and surjective on `[0, total)`.

Raw Lean 4 + Init; hand-rolled clean Nat arithmetic (Init's cancel lemmas leak propext).  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean Nat plumbing -/

/-- `(start + amount) - start = amount`, hand-rolled clean. -/
private theorem addSubCancelLeft : (start amount : Nat) → (start + amount) - start = amount
  | 0, amount => by rw [Nat.zero_add, Nat.sub_zero]
  | start + 1, amount => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeft start amount

/-- `n + 1 - 1 = n`, definitionally. -/
private theorem succSubOne (naturalNumber : Nat) : naturalNumber + 1 - 1 = naturalNumber := rfl

/-! ## The boundary position stays in range -/

/-- ★ **The boundary linearization maps `[0, total)` into `[0, total)`.**  A bottom index keeps its value
(below `bottomCount ≤ total`); a top index lands at `bottomCount + (total-1-index)`, which sits below
`total` since the reversal offset `total-1-index` is strictly below `total-bottomCount`. -/
theorem boundaryPosition_lt (bottomCount total index : Nat) (indexBelow : index < total) :
    boundaryPosition bottomCount total index < total := by
  unfold boundaryPosition
  cases Nat.lt_or_ge index bottomCount with
  | inl below => rw [if_pos below]; exact indexBelow
  | inr atLeast =>
      rw [if_neg (fun lt => Nat.lt_irrefl index (Nat.lt_of_lt_of_le lt atLeast))]
      obtain ⟨gap, gapEq⟩ := Nat.le.dest indexBelow
      obtain ⟨seedOffset, seedEq⟩ := Nat.le.dest atLeast
      have totalPredEq : total - 1 = index + gap := by
        rw [← gapEq, Nat.add_right_comm index 1 gap, succSubOne]
      rw [totalPredEq, addSubCancelLeft index gap, ← gapEq, ← seedEq]
      exact Nat.add_lt_add_right
        (Nat.lt_succ_of_le (Nat.le_add_right bottomCount seedOffset)) gap

/-! ## The boundary position is its own inverse -/

/-- ★ **The boundary linearization is an involution on `[0, total)`.**  Applying `boundaryPosition
bottomCount total` twice to any `index < total` returns `index`: bottom indices are fixed, and the top
reversal `index ↦ bottomCount + (total-1-index)` composed with itself is the identity. -/
theorem boundaryPosition_involutive (bottomCount total index : Nat) (indexBelow : index < total) :
    boundaryPosition bottomCount total (boundaryPosition bottomCount total index) = index := by
  cases Nat.lt_or_ge index bottomCount with
  | inl below =>
      have innerEq : boundaryPosition bottomCount total index = index := by
        unfold boundaryPosition; rw [if_pos below]
      rw [innerEq]
      unfold boundaryPosition; rw [if_pos below]
  | inr atLeast =>
      obtain ⟨seedOffset, seedEq⟩ := Nat.le.dest atLeast
      obtain ⟨gap, gapEq⟩ := Nat.le.dest indexBelow
      have totalPredEq : total - 1 = index + gap := by
        rw [← gapEq, Nat.add_right_comm index 1 gap, succSubOne]
      have bpEq : boundaryPosition bottomCount total index = bottomCount + gap := by
        unfold boundaryPosition
        rw [if_neg (fun lt => Nat.lt_irrefl index (Nat.lt_of_lt_of_le lt atLeast)), totalPredEq,
          addSubCancelLeft index gap]
      rw [bpEq]
      unfold boundaryPosition
      rw [if_neg (fun lt => Nat.lt_irrefl bottomCount
        (Nat.lt_of_le_of_lt (Nat.le_add_right bottomCount gap) lt)), totalPredEq, ← seedEq,
        Nat.add_right_comm bottomCount seedOffset gap, addSubCancelLeft (bottomCount + gap) seedOffset]

/-! ## Surjectivity from the involution -/

/-- ★ **The boundary linearization hits every position in `[0, total)`.**  For any `position < total`,
`boundaryPosition bottomCount total position` is itself a valid index whose image is `position` (the
involution witness).  This is the surjectivity the short-chord minimal-gap argument consumes. -/
theorem boundaryPosition_surjective (bottomCount total position : Nat) (positionBelow : position < total) :
    ∃ index, index < total ∧ boundaryPosition bottomCount total index = position :=
  ⟨boundaryPosition bottomCount total position,
    boundaryPosition_lt bottomCount total position positionBelow,
    boundaryPosition_involutive bottomCount total position positionBelow⟩

/-! ## Injectivity from the involution -/

/-- ★ **The boundary linearization is injective on `[0, total)`.**  Equal images under an involution force
equal arguments — apply `boundaryPosition` again and use `boundaryPosition_involutive` on both. -/
theorem boundaryPosition_injective (bottomCount total firstIndex secondIndex : Nat)
    (firstBelow : firstIndex < total) (secondBelow : secondIndex < total)
    (imagesEqual : boundaryPosition bottomCount total firstIndex
      = boundaryPosition bottomCount total secondIndex) :
    firstIndex = secondIndex := by
  have firstBack := boundaryPosition_involutive bottomCount total firstIndex firstBelow
  have secondBack := boundaryPosition_involutive bottomCount total secondIndex secondBelow
  rw [imagesEqual, secondBack] at firstBack
  exact firstBack.symm

/-! ## Honesty marker -/

/-- **Honesty marker — the boundary linearization is a BIJECTION on `[0, total)` (cup rung D2-prep).**
`boundaryPosition_lt` (maps `[0, total)` into itself), `boundaryPosition_involutive` (its own inverse
there), `boundaryPosition_surjective`, and `boundaryPosition_injective`.  This is the bijection the
short-chord minimal-gap argument (D2, `IsNonCrossing` ⟹ innermost adjacent-matched pair) rests on.  What
this marker does NOT claim: the short-chord lemma itself (D2) or the leg-aligned cup selector (D1).
`= true`. -/
def fxMode_hasBoundaryPositionBijection : Bool := true

end FX1Poly.Polygraph
