import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexValues

/-! # ArcCupReindexInjectivity — the cup-head reindexing is injective

The last value atom of the cup-head seed component correspondence: the reindexing never
identifies two probes, stated at the Bool level as the beq correspondence
`(sigma probeLeft == sigma probeRight) = (probeLeft == probeRight)` — exactly the
`componentCorr` hypothesis the join-transport kit needs over EMPTY link lists, where
`isSameComponent` is definitionally `==`.

Below the tail boundary injectivity comes from a value-recovery LEFT INVERSE: reading the
zones backwards (identity below the window, the two legs back to the window pair, the
displaced suffix back up by two) recovers every probe, so equal values force equal probes by
one `congrArg`.  Across the boundary the zones cannot collide (below-boundary values stay
below `bottomCount + 2`, above-boundary values translate past it), and above it the
translation is plainly injective.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The value-recovery map for the cup head: identity below the window, the two legs back to
the window pair, everything else (the displaced range suffix) back UP by two.  Only its
left-inverse property below the tail boundary matters; it is scaffolding for injectivity. -/
private def cupHeadRecover (bottomCount windowPosition value : Nat) : Nat :=
  if value < windowPosition then value
  else if value = bottomCount then windowPosition
  else if value = bottomCount + 1 then windowPosition + 1
  else value + 2

/-- The recovery map inverts the cup-head reindexing on every below-boundary probe —
four-zone trichotomy, each zone's read landing in a disjoint value range. -/
private theorem cupHeadRecover_leftInverse (bottomCount windowPosition probeIndex : Nat)
    (windowFits : windowPosition ≤ bottomCount) (probeBelow : probeIndex < bottomCount + 2) :
    cupHeadRecover bottomCount windowPosition
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeIndex) = probeIndex := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [arcCupHeadReindex_belowWindow bottomCount windowPosition probeIndex windowFits
        belowWindow]
      show (if probeIndex < windowPosition then probeIndex
          else if probeIndex = bottomCount then windowPosition
          else if probeIndex = bottomCount + 1 then windowPosition + 1
          else probeIndex + 2) = probeIndex
      exact if_pos belowWindow
  | inr atWindowOrPast =>
      cases Nat.lt_or_ge probeIndex (windowPosition + 1) with
      | inl belowSucc =>
          have probeIsWindow : probeIndex = windowPosition :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ belowSucc) atWindowOrPast
          rw [probeIsWindow, arcCupHeadReindex_leftLeg bottomCount windowPosition windowFits]
          show (if bottomCount < windowPosition then bottomCount
              else if bottomCount = bottomCount then windowPosition
              else if bottomCount = bottomCount + 1 then windowPosition + 1
              else bottomCount + 2) = windowPosition
          exact (if_neg (fun below =>
              Nat.lt_irrefl bottomCount (Nat.lt_of_lt_of_le below windowFits))).trans
            (if_pos rfl)
      | inr atLeastSucc =>
          cases Nat.lt_or_ge probeIndex (windowPosition + 2) with
          | inl belowTwo =>
              have probeIsRight : probeIndex = windowPosition + 1 :=
                Nat.le_antisymm (Nat.le_of_succ_le_succ belowTwo) atLeastSucc
              rw [probeIsRight,
                arcCupHeadReindex_rightLeg bottomCount windowPosition windowFits]
              show (if bottomCount + 1 < windowPosition then bottomCount + 1
                  else if bottomCount + 1 = bottomCount then windowPosition
                  else if bottomCount + 1 = bottomCount + 1 then windowPosition + 1
                  else bottomCount + 1 + 2) = windowPosition + 1
              exact (if_neg (fun below => Nat.lt_irrefl bottomCount
                  (Nat.lt_of_succ_lt (Nat.lt_of_lt_of_le below windowFits)))).trans
                ((if_neg (fun legsCollide => Nat.lt_irrefl bottomCount
                    (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount)
                      (Nat.le_of_eq legsCollide)))).trans
                  (if_pos rfl))
          | inr pastWindow =>
              obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest pastWindow
              have indexForm : windowPosition + pastOffset + 2 = probeIndex := by
                rw [Nat.add_right_comm windowPosition pastOffset 2]
                exact offsetSpec
              have pastBound : windowPosition + pastOffset < bottomCount := by
                have shifted : windowPosition + pastOffset + 2 < bottomCount + 2 := by
                  rw [indexForm]
                  exact probeBelow
                exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ shifted)
              rw [← indexForm,
                arcCupHeadReindex_pastWindow bottomCount windowPosition pastOffset pastBound]
              show (if windowPosition + pastOffset < windowPosition
                    then windowPosition + pastOffset
                  else if windowPosition + pastOffset = bottomCount then windowPosition
                  else if windowPosition + pastOffset = bottomCount + 1
                    then windowPosition + 1
                  else windowPosition + pastOffset + 2) = windowPosition + pastOffset + 2
              exact (if_neg (fun below => Nat.lt_irrefl windowPosition
                  (Nat.lt_of_le_of_lt (Nat.le_add_right windowPosition pastOffset)
                    below))).trans
                ((if_neg (fun hitsLeft => Nat.lt_irrefl bottomCount
                    (Nat.lt_of_le_of_lt (Nat.le_of_eq hitsLeft.symm) pastBound))).trans
                  (if_neg (fun hitsRight => Nat.lt_irrefl bottomCount
                    (Nat.lt_of_succ_lt (Nat.lt_of_le_of_lt (Nat.le_of_eq hitsRight.symm)
                      pastBound)))))

/-- ★ **The cup-head reindexing is injective** — below the boundary by the recovery left
inverse, above it by the translation, across by the disjoint value ranges. -/
theorem arcCupHeadReindex_injective (bottomCount windowPosition probeLeft probeRight : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (valuesEqual : arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft
      = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight) :
    probeLeft = probeRight := by
  cases Nat.lt_or_ge probeLeft (bottomCount + 2) with
  | inl leftBelow =>
      cases Nat.lt_or_ge probeRight (bottomCount + 2) with
      | inl rightBelow =>
          have recovered :=
            congrArg (cupHeadRecover bottomCount windowPosition) valuesEqual
          rw [cupHeadRecover_leftInverse bottomCount windowPosition probeLeft windowFits
              leftBelow,
            cupHeadRecover_leftInverse bottomCount windowPosition probeRight windowFits
              rightBelow] at recovered
          exact recovered
      | inr rightAbove =>
          have leftValue := arcCupHeadReindex_valueBelowBoundary bottomCount windowPosition
            probeLeft windowFits leftBelow
          rw [arcHeadReindex_cupSeedShifts bottomCount windowPosition probeRight rightAbove]
            at valuesEqual
          exact (Nat.lt_irrefl (probeRight + 1) (Nat.lt_trans
            (Nat.lt_of_le_of_lt (Nat.le_of_eq valuesEqual.symm) leftValue)
            (Nat.succ_le_succ rightAbove))).elim
  | inr leftAbove =>
      cases Nat.lt_or_ge probeRight (bottomCount + 2) with
      | inl rightBelow =>
          have rightValue := arcCupHeadReindex_valueBelowBoundary bottomCount windowPosition
            probeRight windowFits rightBelow
          rw [arcHeadReindex_cupSeedShifts bottomCount windowPosition probeLeft leftAbove]
            at valuesEqual
          exact (Nat.lt_irrefl (probeLeft + 1) (Nat.lt_trans
            (Nat.lt_of_le_of_lt (Nat.le_of_eq valuesEqual) rightValue)
            (Nat.succ_le_succ leftAbove))).elim
      | inr rightAbove =>
          rw [arcHeadReindex_cupSeedShifts bottomCount windowPosition probeLeft leftAbove,
            arcHeadReindex_cupSeedShifts bottomCount windowPosition probeRight rightAbove]
            at valuesEqual
          exact Nat.succ.inj valuesEqual

/-- ★ **The Bool beq correspondence** — the `componentCorr` atom of the seed component
correspondence: over empty link lists `isSameComponent` is definitionally `==`, so this IS
the transport hypothesis of the join kit at the cup seed. -/
theorem arcCupHeadReindex_beqCorr (bottomCount windowPosition probeLeft probeRight : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeLeft
      == arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeRight)
      = (probeLeft == probeRight) := by
  cases Nat.decEq probeLeft probeRight with
  | isTrue probesEqual =>
      rw [probesEqual]
      have valueSelfTrue : (arcHeadReindex (natListInsertAt (List.range bottomCount)
            windowPosition [bottomCount, bottomCount + 1]) 1 probeRight
          == arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1 probeRight) = true := decide_eq_true rfl
      have probeSelfTrue : (probeRight == probeRight) = true := decide_eq_true rfl
      rw [valueSelfTrue, probeSelfTrue]
  | isFalse probesDiffer =>
      have valuesFalse : (arcHeadReindex (natListInsertAt (List.range bottomCount)
            windowPosition [bottomCount, bottomCount + 1]) 1 probeLeft
          == arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1 probeRight) = false :=
        decide_eq_false (fun valuesEqual =>
          probesDiffer (arcCupHeadReindex_injective bottomCount windowPosition probeLeft
            probeRight windowFits valuesEqual))
      have probesFalse : (probeLeft == probeRight) = false := decide_eq_false probesDiffer
      rw [valuesFalse, probesFalse]

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head reindexing's injectivity atom (peel campaign H, seed
rung, LINKS-leg atoms, part 2).**  The value-recovery left inverse (four-zone trichotomy),
propositional injectivity (below via recovery, above via the translation, across via the
disjoint value ranges), and the Bool beq correspondence — the `componentCorr` hypothesis of
the join-transport kit at the cup seed.  What this marker does NOT claim: the assembled seed
`ArcComponentShiftCorr` at the cup head (the two-join kit assembly) and the cap-head
analogues.  `= true`. -/
def fxMode_hasArcCupHeadReindexInjectivity : Bool := true

end FX1Poly.Polygraph
