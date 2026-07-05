import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # MatchingScanFallback — the no-passer fallback and the two-zone shift discipline

The partner scan's FALLBACK characterization in PROPOSITION form: when no scanned candidate
other than the exclude passes the root test, the scan returns the exclude — the thin
corollary of the Bool-test form (`findPartnerScan_eqExclude_ofAllFail`) in the shape the
census refutations produce, evaluating a partner at an orphaned component (a component
whose only boundary token is the probe itself).

Alongside it, the two-zone shift's index discipline: `freshShiftAbove threshold 2` is
injective and its image avoids the window pair `{threshold, threshold + 1}` — the facts
every per-index dispatch over shift-image candidates needs.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Boolean plumbing (per-file copy, following the codebase pattern) -/

private theorem ne_ofBneTrue {leftValue rightValue : Nat}
    (bneTrue : (leftValue != rightValue) = true) : leftValue ≠ rightValue := fun valuesEq => by
  have selfBne : (rightValue != rightValue) = false := by
    show (!(rightValue == rightValue)) = false
    have selfBeq : (rightValue == rightValue) = true := decide_eq_true rfl
    rw [selfBeq]
    rfl
  rw [valuesEq, selfBne] at bneTrue
  exact Bool.noConfusion bneTrue

/-! ## The no-passer fallback -/

/-- ★ **Scan fallback, proposition form**: when no scanned candidate other than the exclude
passes the root test, the partner scan returns the exclude — the converse of scan
completeness, as the corollary of the Bool-test form. -/
theorem findPartnerScan_eqExclude_ofNoPasser (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat)
    (scanned : List Nat)
    (noPasser : ∀ candidate, candidate ∈ scanned → candidate ≠ excludeIndex →
      unionFindRootOf links (natListGetAt boundaryNodes candidate) = rootHere → False) :
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned = excludeIndex :=
  findPartnerScan_eqExclude_ofAllFail links boundaryNodes rootHere excludeIndex scanned
    (fun candidate candidateMem => by
      cases bneTest : (candidate != excludeIndex) with
      | false => rfl
      | true =>
          cases beqTest : (unionFindRootOf links (natListGetAt boundaryNodes candidate)
              == rootHere) with
          | false => rfl
          | true =>
              exact False.elim (noPasser candidate candidateMem
                (ne_ofBneTrue bneTest) (of_decide_eq_true beqTest)))

/-! ## The two-zone shift's index discipline -/

/-- **The two-zone shift is injective**: below the threshold it is the identity, at or past
it adds two — the zones' images are disjoint, and each zone is injective. -/
theorem freshShiftAbove_two_injective (threshold firstValue secondValue : Nat)
    (imagesEqual : freshShiftAbove threshold 2 firstValue
      = freshShiftAbove threshold 2 secondValue) :
    firstValue = secondValue := by
  cases Nat.lt_or_ge firstValue threshold with
  | inl firstBelow =>
      rw [freshShiftAbove_ofNotLe threshold 2 firstValue
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe firstBelow))] at imagesEqual
      cases Nat.lt_or_ge secondValue threshold with
      | inl secondBelow =>
          rw [freshShiftAbove_ofNotLe threshold 2 secondValue
            (fun thresholdLe => Nat.lt_irrefl threshold
              (Nat.lt_of_le_of_lt thresholdLe secondBelow))] at imagesEqual
          exact imagesEqual
      | inr secondAtOrPast =>
          rw [freshShiftAbove_ofLe threshold 2 secondValue secondAtOrPast] at imagesEqual
          exact False.elim (Nat.lt_irrefl firstValue
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_lt_of_le firstBelow
                (Nat.le_trans secondAtOrPast (Nat.le_add_right secondValue 2)))
              (Nat.le_of_eq imagesEqual.symm)))
  | inr firstAtOrPast =>
      rw [freshShiftAbove_ofLe threshold 2 firstValue firstAtOrPast] at imagesEqual
      cases Nat.lt_or_ge secondValue threshold with
      | inl secondBelow =>
          rw [freshShiftAbove_ofNotLe threshold 2 secondValue
            (fun thresholdLe => Nat.lt_irrefl threshold
              (Nat.lt_of_le_of_lt thresholdLe secondBelow))] at imagesEqual
          exact False.elim (Nat.lt_irrefl secondValue
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_lt_of_le secondBelow
                (Nat.le_trans firstAtOrPast (Nat.le_add_right firstValue 2)))
              (Nat.le_of_eq imagesEqual)))
      | inr secondAtOrPast =>
          rw [freshShiftAbove_ofLe threshold 2 secondValue secondAtOrPast] at imagesEqual
          exact Nat.succ.inj (Nat.succ.inj imagesEqual)

/-- **The shift image avoids the left window index**: below-zone images stay below the
threshold, at-or-past-zone images land at least two past it. -/
theorem freshShiftAbove_neWindow (threshold value : Nat) :
    freshShiftAbove threshold 2 value ≠ threshold := by
  cases Nat.lt_or_ge value threshold with
  | inl below =>
      rw [freshShiftAbove_ofNotLe threshold 2 value
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe below))]
      exact fun valueEq => Nat.lt_irrefl value
        (Nat.lt_of_lt_of_le below (Nat.le_of_eq valueEq.symm))
  | inr atOrPast =>
      rw [freshShiftAbove_ofLe threshold 2 value atOrPast]
      exact fun imageEq => Nat.lt_irrefl threshold
        (Nat.lt_of_le_of_lt atOrPast
          (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ value))
            (Nat.le_of_eq imageEq)))

/-- **The shift image avoids the right window index** — the mirror at `threshold + 1`. -/
theorem freshShiftAbove_neWindowSucc (threshold value : Nat) :
    freshShiftAbove threshold 2 value ≠ threshold + 1 := by
  cases Nat.lt_or_ge value threshold with
  | inl below =>
      rw [freshShiftAbove_ofNotLe threshold 2 value
        (fun thresholdLe => Nat.lt_irrefl threshold
          (Nat.lt_of_le_of_lt thresholdLe below))]
      exact fun valueEq => Nat.lt_irrefl value
        (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le below (Nat.le_succ threshold))
          (Nat.le_of_eq valueEq.symm))
  | inr atOrPast =>
      rw [freshShiftAbove_ofLe threshold 2 value atOrPast]
      exact fun imageEq => Nat.lt_irrefl (threshold + 1)
        (Nat.lt_of_le_of_lt (Nat.succ_le_succ atOrPast)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self (value + 1))
            (Nat.le_of_eq imageEq)))

/-- **Honesty marker — the scan fallback and the shift index discipline are SHIPPED (peel
campaign H, cup rung 4).**  The no-passer fallback
(`findPartnerScan_eqExclude_ofNoPasser`), the two-zone shift injectivity
(`freshShiftAbove_two_injective`), and the window-avoidance facts
(`freshShiftAbove_neWindow` / `...Succ`).  What this marker does NOT claim: the
degenerate-leg fallback pin at the cup composite and the assembled cup partner list.
`= true`. -/
def fxMode_hasMatchingScanFallback : Bool := true

end FX1Poly.Polygraph
