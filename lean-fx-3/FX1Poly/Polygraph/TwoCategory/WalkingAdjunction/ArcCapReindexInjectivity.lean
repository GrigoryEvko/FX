import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapReindexValues

/-! # ArcCapReindexInjectivity — the cap-head reindexing is injective

The cap-head mirror of the cup injectivity atom.  The cap reindexing moves values UP
(identity below the window, up by two past it, up by three above the tail boundary), so no
subtraction-free recovery map exists; injectivity instead goes by direct zone-pair analysis.
The three zones' value ranges are disjoint — `[0, windowPosition)`,
`[windowPosition + 2, bottomCount)`, `[bottomCount + 1, ...)` — so the six mixed pairs refute
by range separation and the three diagonal pairs cancel their common translation.

Packaged as the Bool beq correspondence `(sigma probeLeft == sigma probeRight) = (probeLeft
== probeRight)` — over empty link lists `isSameComponent` is definitionally `==`, so this IS
the pointwise hypothesis of the join-transport kit at the cap seed.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cap-head reindexing is injective** — diagonal zone pairs cancel the common
translation, mixed zone pairs refute by the disjoint value ranges. -/
theorem arcCapHeadReindex_injective
    (bottomCount windowPosition tailBoundary probeLeft probeRight : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (valuesEqual : arcHeadReindex
        (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeLeft
      = arcHeadReindex
        (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeRight) :
    probeLeft = probeRight := by
  cases Nat.lt_or_ge probeLeft windowPosition with
  | inl belowWindowLeft =>
      rw [arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary probeLeft
        windowFits tailBoundaryFits belowWindowLeft] at valuesEqual
      cases Nat.lt_or_ge probeRight windowPosition with
      | inl belowWindowRight =>
          rw [arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary
            probeRight windowFits tailBoundaryFits belowWindowRight] at valuesEqual
          exact valuesEqual
      | inr atWindowRight =>
          cases Nat.lt_or_ge probeRight tailBoundary with
          | inl belowTailRight =>
              obtain ⟨rightOffset, rightSpec⟩ := Nat.le.dest atWindowRight
              have rightBound : windowPosition + rightOffset < tailBoundary := by
                rw [rightSpec]
                exact belowTailRight
              rw [← rightSpec,
                arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary
                  rightOffset windowFits tailBoundaryFits rightBound] at valuesEqual
              exact (Nat.lt_irrefl probeLeft (Nat.lt_of_lt_of_le
                (Nat.lt_of_lt_of_le belowWindowLeft
                  (Nat.le_trans (Nat.le_add_right windowPosition rightOffset)
                    (Nat.le_trans (Nat.le_succ (windowPosition + rightOffset))
                      (Nat.le_succ (windowPosition + rightOffset + 1)))))
                (Nat.le_of_eq valuesEqual.symm))).elim
          | inr atTailRight =>
              rw [arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary
                windowFits tailBoundaryFits probeRight atTailRight] at valuesEqual
              exact (Nat.lt_irrefl probeLeft (Nat.lt_of_lt_of_le
                (Nat.lt_of_lt_of_le belowWindowLeft
                  (Nat.le_trans (Nat.le_trans (Nat.le_add_right windowPosition 2) windowFits)
                    (Nat.le_trans
                      (Nat.le_trans (Nat.le_of_eq tailBoundaryFits.symm)
                        (Nat.succ_le_succ (Nat.succ_le_succ atTailRight)))
                      (Nat.le_succ (probeRight + 2)))))
                (Nat.le_of_eq valuesEqual.symm))).elim
  | inr atWindowLeft =>
      cases Nat.lt_or_ge probeLeft tailBoundary with
      | inl belowTailLeft =>
          obtain ⟨leftOffset, leftSpec⟩ := Nat.le.dest atWindowLeft
          have leftBound : windowPosition + leftOffset < tailBoundary := by
            rw [leftSpec]
            exact belowTailLeft
          rw [← leftSpec] at valuesEqual ⊢
          rw [arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary
            leftOffset windowFits tailBoundaryFits leftBound] at valuesEqual
          cases Nat.lt_or_ge probeRight windowPosition with
          | inl belowWindowRight =>
              rw [arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary
                probeRight windowFits tailBoundaryFits belowWindowRight] at valuesEqual
              exact (Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt
                (Nat.le_trans
                  (Nat.le_trans (Nat.le_add_right windowPosition leftOffset)
                    (Nat.le_trans (Nat.le_succ (windowPosition + leftOffset))
                      (Nat.le_succ (windowPosition + leftOffset + 1))))
                  (Nat.le_of_eq valuesEqual))
                belowWindowRight)).elim
          | inr atWindowRight =>
              cases Nat.lt_or_ge probeRight tailBoundary with
              | inl belowTailRight =>
                  obtain ⟨rightOffset, rightSpec⟩ := Nat.le.dest atWindowRight
                  have rightBound : windowPosition + rightOffset < tailBoundary := by
                    rw [rightSpec]
                    exact belowTailRight
                  rw [← rightSpec] at valuesEqual ⊢
                  rw [arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary
                    rightOffset windowFits tailBoundaryFits rightBound] at valuesEqual
                  exact Nat.succ.inj (Nat.succ.inj valuesEqual)
              | inr atTailRight =>
                  rw [arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary
                    windowFits tailBoundaryFits probeRight atTailRight] at valuesEqual
                  have valueBelowBoundary :
                      windowPosition + leftOffset + 2 < bottomCount :=
                    Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ leftBound))
                      (Nat.le_of_eq tailBoundaryFits)
                  have boundaryBelowShifted : bottomCount < probeRight + 3 :=
                    Nat.lt_of_le_of_lt
                      (Nat.le_trans (Nat.le_of_eq tailBoundaryFits.symm)
                        (Nat.succ_le_succ (Nat.succ_le_succ atTailRight)))
                      (Nat.lt_succ_self (probeRight + 2))
                  exact (Nat.lt_irrefl (windowPosition + leftOffset + 2)
                    (Nat.lt_of_lt_of_le
                      (Nat.lt_trans valueBelowBoundary boundaryBelowShifted)
                      (Nat.le_of_eq valuesEqual.symm))).elim
      | inr atTailLeft =>
          rw [arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary
            windowFits tailBoundaryFits probeLeft atTailLeft] at valuesEqual
          cases Nat.lt_or_ge probeRight windowPosition with
          | inl belowWindowRight =>
              rw [arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary
                probeRight windowFits tailBoundaryFits belowWindowRight] at valuesEqual
              exact (Nat.lt_irrefl (probeLeft + 3) (Nat.lt_of_lt_of_le
                (Nat.lt_of_le_of_lt (Nat.le_of_eq valuesEqual) belowWindowRight)
                (Nat.le_trans (Nat.le_trans (Nat.le_add_right windowPosition 2) windowFits)
                  (Nat.le_trans
                    (Nat.le_trans (Nat.le_of_eq tailBoundaryFits.symm)
                      (Nat.succ_le_succ (Nat.succ_le_succ atTailLeft)))
                    (Nat.le_succ (probeLeft + 2)))))).elim
          | inr atWindowRight =>
              cases Nat.lt_or_ge probeRight tailBoundary with
              | inl belowTailRight =>
                  obtain ⟨rightOffset, rightSpec⟩ := Nat.le.dest atWindowRight
                  have rightBound : windowPosition + rightOffset < tailBoundary := by
                    rw [rightSpec]
                    exact belowTailRight
                  rw [← rightSpec,
                    arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary
                      rightOffset windowFits tailBoundaryFits rightBound] at valuesEqual
                  have valueBelowBoundary :
                      windowPosition + rightOffset + 2 < bottomCount :=
                    Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ rightBound))
                      (Nat.le_of_eq tailBoundaryFits)
                  have boundaryBelowShifted : bottomCount < probeLeft + 3 :=
                    Nat.lt_of_le_of_lt
                      (Nat.le_trans (Nat.le_of_eq tailBoundaryFits.symm)
                        (Nat.succ_le_succ (Nat.succ_le_succ atTailLeft)))
                      (Nat.lt_succ_self (probeLeft + 2))
                  exact (Nat.lt_irrefl bottomCount (Nat.lt_trans
                    (Nat.lt_of_lt_of_le boundaryBelowShifted (Nat.le_of_eq valuesEqual))
                    valueBelowBoundary)).elim
              | inr atTailRight =>
                  rw [arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary
                    windowFits tailBoundaryFits probeRight atTailRight] at valuesEqual
                  exact Nat.succ.inj (Nat.succ.inj (Nat.succ.inj valuesEqual))

/-- ★ **The Bool beq correspondence** — the pointwise hypothesis of the join-transport kit
at the cap seed: over empty link lists `isSameComponent` is definitionally `==`, so this IS
the cap analogue of the cup `componentCorr` atom. -/
theorem arcCapHeadReindex_beqCorr
    (bottomCount windowPosition tailBoundary probeLeft probeRight : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeLeft
      == arcHeadReindex
        (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeRight)
      = (probeLeft == probeRight) := by
  cases Nat.decEq probeLeft probeRight with
  | isTrue probesEqual =>
      rw [probesEqual]
      have valueSelfTrue : (arcHeadReindex
            (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeRight
          == arcHeadReindex
            (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeRight)
          = true := decide_eq_true rfl
      have probeSelfTrue : (probeRight == probeRight) = true := decide_eq_true rfl
      rw [valueSelfTrue, probeSelfTrue]
  | isFalse probesDiffer =>
      have valuesFalse : (arcHeadReindex
            (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeLeft
          == arcHeadReindex
            (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeRight)
          = false :=
        decide_eq_false (fun valuesEqual =>
          probesDiffer (arcCapHeadReindex_injective bottomCount windowPosition tailBoundary
            probeLeft probeRight windowFits tailBoundaryFits valuesEqual))
      have probesFalse : (probeLeft == probeRight) = false := decide_eq_false probesDiffer
      rw [valuesFalse, probesFalse]

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-head reindexing's injectivity atom (peel campaign H, seed
rung, cap LINKS-leg atoms, part 2).**  Propositional injectivity by direct zone-pair
analysis (three diagonal translation cancellations, six mixed range-separation refutations —
no recovery map, since the cap reindexing moves values up and the codebase bans Nat
subtraction here), and the Bool beq correspondence — the pointwise hypothesis of the
join-transport kit at the cap seed.  What this marker does NOT claim: the assembled cap-seed
`ArcComponentShiftCorr` (with its degenerate legs) and the extract correspondence.
`= true`. -/
def fxMode_hasArcCapHeadReindexInjectivity : Bool := true

end FX1Poly.Polygraph
