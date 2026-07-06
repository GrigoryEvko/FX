import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexValues

/-! # ArcCupReindexInjective — the cup-head reindexing is injective (peel campaign H, seed rung, LINKS-leg atoms, part 2)

The seed component correspondence (`ArcComponentShiftCorr` at the cup head) needs the cup-head
reindexing's INJECTIVITY atom — deferred by `ArcCupReindexValues`.  This brick builds the
VALUE-RECOVERY left inverse `arcCupHeadReindexRecover` (piecewise by value zone, inverting each of
the reindexing's four value zones the previous brick pinned) and proves:

  * `arcCupHeadReindex_recoverLeftInverse` — the recover is a genuine left inverse, by the same
    four-zone trichotomy on the probe the value bound used, discharging each zone with its shipped
    zone read (`arcCupHeadReindex_belowWindow` / `…leftLeg` / `…rightLeg` / `…pastWindow` and the
    above-boundary `arcHeadReindex_cupSeedShifts`);
  * `arcCupHeadReindex_injective` — the reindexing is injective, immediate from the left inverse;
  * `arcCupHeadReindex_beqTransport` — the `BEq` transport `(sigma p == sigma q) = (p == q)` the
    component queries consume, by casing both Bools against injectivity + congruence.

The assembled seed `ArcComponentShiftCorr` at the cup head (event-absorbed, leg-preimage-reindexed)
and the cap-head analogues remain for the next bricks.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The value-recovery left inverse of the cup-head reindexing.**  Inverts each value zone of
`arcHeadReindex (cup wires) 1`: below the window the value is its own preimage; a value in
`[windowPosition, bottomCount)` came from the displaced range suffix (preimage `value + 2`); the two
fresh legs `bottomCount` / `bottomCount + 1` came from the window pair; any higher value came from
the shifted-up tail (preimage `value - 1`).  The event node `bottomCount + 2` is never an image, so
its recover value is immaterial. -/
def arcCupHeadReindexRecover (bottomCount windowPosition value : Nat) : Nat :=
  if value < windowPosition then value
  else if value < bottomCount then value + 2
  else if value = bottomCount then windowPosition
  else if value = bottomCount + 1 then windowPosition + 1
  else value - 1

/-- ★ **The recover is a left inverse of the cup-head reindexing.**  Four-zone trichotomy on the
probe: below the window (identity read), at the window / its successor (the two legs), past the
window below the boundary (shift-down read), and at or above the tail boundary (shift-up read).
Each zone rewrites the reindexing by its shipped value read, then recomputes the recover on the
resulting value. -/
theorem arcCupHeadReindex_recoverLeftInverse (bottomCount windowPosition probeIndex : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    arcCupHeadReindexRecover bottomCount windowPosition
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeIndex) = probeIndex := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [arcCupHeadReindex_belowWindow bottomCount windowPosition probeIndex windowFits
        belowWindow]
      unfold arcCupHeadReindexRecover
      rw [if_pos belowWindow]
  | inr atWindowOrPast =>
      cases Nat.lt_or_ge probeIndex (windowPosition + 1) with
      | inl belowSucc =>
          have probeIsWindow : probeIndex = windowPosition :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ belowSucc) atWindowOrPast
          rw [probeIsWindow, arcCupHeadReindex_leftLeg bottomCount windowPosition windowFits]
          unfold arcCupHeadReindexRecover
          rw [if_neg (Nat.not_lt.mpr windowFits), if_neg (Nat.lt_irrefl bottomCount), if_pos rfl]
      | inr atLeastSucc =>
          cases Nat.lt_or_ge probeIndex (windowPosition + 2) with
          | inl belowTwo =>
              have probeIsRight : probeIndex = windowPosition + 1 :=
                Nat.le_antisymm (Nat.le_of_succ_le_succ belowTwo) atLeastSucc
              rw [probeIsRight, arcCupHeadReindex_rightLeg bottomCount windowPosition windowFits]
              unfold arcCupHeadReindexRecover
              rw [if_neg (Nat.not_lt.mpr (Nat.le_trans windowFits (Nat.le_succ bottomCount))),
                if_neg (Nat.not_lt.mpr (Nat.le_succ bottomCount)),
                if_neg (Ne.symm (Nat.ne_of_lt (Nat.lt_succ_self bottomCount))), if_pos rfl]
          | inr atLeastTwo =>
              cases Nat.lt_or_ge probeIndex (bottomCount + 2) with
              | inl belowBoundary =>
                  obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest atLeastTwo
                  have indexForm : windowPosition + pastOffset + 2 = probeIndex := by
                    rw [Nat.add_right_comm windowPosition pastOffset 2]
                    exact offsetSpec
                  have pastBound : windowPosition + pastOffset < bottomCount := by
                    have shifted : windowPosition + pastOffset + 2 < bottomCount + 2 := by
                      rw [indexForm]; exact belowBoundary
                    exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ shifted)
                  rw [← indexForm,
                    arcCupHeadReindex_pastWindow bottomCount windowPosition pastOffset pastBound]
                  unfold arcCupHeadReindexRecover
                  rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right windowPosition pastOffset)),
                    if_pos pastBound]
              | inr aboveBoundary =>
                  rw [arcHeadReindex_cupSeedShifts bottomCount windowPosition probeIndex
                    aboveBoundary]
                  have belowThanSucc : bottomCount < probeIndex + 1 :=
                    Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le
                        (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount)
                          (Nat.le_succ (bottomCount + 1)))
                        aboveBoundary)
                      (Nat.le_succ probeIndex)
                  have succBelowThanSucc : bottomCount + 1 < probeIndex + 1 :=
                    Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (bottomCount + 1)) aboveBoundary)
                      (Nat.le_succ probeIndex)
                  unfold arcCupHeadReindexRecover
                  rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt
                        (Nat.lt_of_le_of_lt windowFits belowThanSucc))),
                    if_neg (Nat.not_lt.mpr (Nat.le_of_lt belowThanSucc)),
                    if_neg (Ne.symm (Nat.ne_of_lt belowThanSucc)),
                    if_neg (Ne.symm (Nat.ne_of_lt succBelowThanSucc))]
                  exact Nat.succ_sub_one probeIndex

/-- ★ **The cup-head reindexing is injective** — immediate from the value-recovery left inverse:
equal images recover to equal probes. -/
theorem arcCupHeadReindex_injective (bottomCount windowPosition probeLeft probeRight : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (equalImages :
      arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeLeft
        = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeRight) :
    probeLeft = probeRight := by
  rw [← arcCupHeadReindex_recoverLeftInverse bottomCount windowPosition probeLeft windowFits,
    ← arcCupHeadReindex_recoverLeftInverse bottomCount windowPosition probeRight windowFits,
    equalImages]

/-- ★ **The `BEq` transport the component queries consume** — the cup-head reindexing carries `Nat`
equality both ways: `(sigma p == sigma q) = (p == q)`.  Case on both Bool values; the mismatched
corners are refuted by injectivity (`sigma p = sigma q → p = q`) and by congruence
(`p = q → sigma p = sigma q`).  The leg-preimage facts the seed correspondence needs
(`(sigma p == bottomCount) = (p == windowPosition)`, and the `bottomCount + 1` analogue) are
instances after rewriting `bottomCount = sigma windowPosition` by the shipped `…leftLeg` read. -/
theorem arcCupHeadReindex_beqTransport (bottomCount windowPosition probeLeft probeRight : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeLeft
        == arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeRight)
      = (probeLeft == probeRight) := by
  cases hProbes : (probeLeft == probeRight) with
  | true =>
      have probesEqual : probeLeft = probeRight := of_decide_eq_true hProbes
      cases hImages : (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeLeft
        == arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeRight) with
      | true => rfl
      | false =>
          exact absurd
            (congrArg (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
              [bottomCount, bottomCount + 1]) 1) probesEqual)
            (of_decide_eq_false hImages)
  | false =>
      have probesDistinct : probeLeft ≠ probeRight := of_decide_eq_false hProbes
      cases hImages : (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeLeft
        == arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeRight) with
      | true =>
          exact absurd
            (arcCupHeadReindex_injective bottomCount windowPosition probeLeft probeRight windowFits
              (of_decide_eq_true hImages))
            probesDistinct
      | false => rfl

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head reindexing is INJECTIVE + carries `Nat` equality (peel campaign
H, seed rung, LINKS-leg atoms, part 2).**  `arcCupHeadReindexRecover` (the piecewise value-recovery
inverse), `arcCupHeadReindex_recoverLeftInverse` (left inverse by the four-zone trichotomy on the
probe, each zone discharged by its shipped `ArcCupReindexValues` read), `arcCupHeadReindex_injective`
(injectivity from the left inverse), and `arcCupHeadReindex_beqTransport` (the `BEq` transport
`(sigma p == sigma q) = (p == q)` the component queries consume, via injectivity + congruence).
What this marker does NOT claim: the assembled seed `ArcComponentShiftCorr` at the cup head (the
event-absorbed, leg-preimage-reindexed component correspondence) and the cap-head analogues.
`= true`. -/
def fxMode_hasArcCupReindexInjective : Bool := true

end FX1Poly.Polygraph
