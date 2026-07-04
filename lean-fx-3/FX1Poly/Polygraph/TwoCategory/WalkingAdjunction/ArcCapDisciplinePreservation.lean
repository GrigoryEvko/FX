import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisciplinePreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapRootAtlas
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCapSwapCore

/-! # ArcCapDisciplinePreservation — the cap step preserves the typed-ends discipline (peel campaign C, rung 2c)

A cap fired at a `tip`-parity window keeps the `ArcOpenEndsDiscipline` invariant.  The cap's
merge genuinely joins two old components, so the transfer runs through the join split
(`isSameComponent_unionFindJoin_true_iff`): a surviving same-component pair either was
already connected (parities ride the two-shift), or is newly connected through the consumed
wires — and there the FORCED-SIDE analysis fires.  A remaining wire tied to the LEFT
consumed wire must sit strictly left of the window (were it right, the pair with the window
would type the window `base`, against the `tip` pin); one tied to the RIGHT consumed wire
must sit strictly right (were it left, the pair would type `window + 1` as `tip`, against
its forced `base` parity).  The two sides compose exactly into the `(base, tip)` typing the
discipline demands, and the crossed pairing is refuted outright by position order.

The window-parity premise (`tip` at the fire position) is discharged at the fold level by
`adjunctionCapAtom_windowPositionMode`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **Old nodes' connectivity through a cap is their MERGED connectivity** — the cap's event
join hangs a fresh node and never moves an old root, so the same-component test at
`stepCapArc` links equals the test at the merged links `unionFindJoin links left right`. -/
theorem isSameComponent_stepCapArc_oldNodes (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh)
    (firstNode secondNode : Nat)
    (firstBelow : firstNode < state.nextFresh) (secondBelow : secondNode < state.nextFresh) :
    isSameComponent (stepCapArc state position).links firstNode secondNode
      = isSameComponent
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          firstNode secondNode := by
  show (unionFindRootOf (stepCapArc state position).links firstNode
      == unionFindRootOf (stepCapArc state position).links secondNode)
    = (unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          firstNode
      == unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          secondNode)
  rw [stepCapArc_root_old state position fresh forest nfPos firstNode
      (capMerge_root_below state position fresh nfPos firstNode firstBelow),
    stepCapArc_root_old state position fresh forest nfPos secondNode
      (capMerge_root_below state position fresh nfPos secondNode secondBelow)]

/-! ## The preservation theorem -/

/-- ★ **A cap fired at a `tip`-parity window preserves the typed-ends discipline.**  Old
pairs transfer through the merged links and split three ways: already-connected pairs ride
the old discipline with two-shift-stable parities; pairs newly connected through the
consumed wires resolve by the forced-side analysis (left-tied wires sit left of the window
at `base`, right-tied wires sit right at `tip`); the crossed pairing contradicts position
order through the window parities. -/
theorem arcOpenEndsDiscipline_stepCapArc (sourceMode : AdjunctionMode)
    (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (windowParityIsTip :
      adjunctionModeAtDistance sourceMode position = AdjunctionMode.tip)
    (discipline : ArcOpenEndsDiscipline sourceMode state) :
    ArcOpenEndsDiscipline sourceMode (stepCapArc state position) := by
  intro lowPosition highPosition lowBelowHigh highInRange sameComponentHolds
  have windowBelowLength : position < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) windowInRange
  have windowSuccBelowLength : position + 1 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) position) windowInRange
  have zeroBelowLength : 0 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.succ_pos (position + 1)) windowInRange
  have nfPos : 0 < state.nextFresh :=
    Nat.lt_of_le_of_lt (Nat.zero_le _)
      (natListGetAt_lt_ofInRange state.nextFresh state.openWires 0 zeroBelowLength fresh.1)
  have windowSuccParityIsBase :
      adjunctionModeAtDistance sourceMode (position + 1) = AdjunctionMode.base :=
    congrArg adjunctionOppositeMode windowParityIsTip
  have highBelowTrimmed :
      highPosition < (natListRemoveTwoAt state.openWires position).length := highInRange
  have trimmedLengthPlusTwo :
      (natListRemoveTwoAt state.openWires position).length + 2 = state.openWires.length :=
    natListRemoveTwoAt_length state.openWires position windowInRange
  cases Nat.lt_or_ge lowPosition position with
  | inl lowBelowPosition =>
      have lowBelowLength : lowPosition < state.openWires.length :=
        Nat.lt_trans lowBelowPosition windowBelowLength
      have lowRead :
          natListGetAt (stepCapArc state position).openWires lowPosition
            = natListGetAt state.openWires lowPosition :=
        natListGetAt_natListRemoveTwoAt_below state.openWires position lowPosition
          lowBelowPosition
      have lowValueBelow : natListGetAt state.openWires lowPosition < state.nextFresh :=
        natListGetAt_lt_ofInRange state.nextFresh state.openWires lowPosition
          lowBelowLength fresh.1
      cases Nat.lt_or_ge highPosition position with
      | inl highBelowPosition =>
          have highBelowLength : highPosition < state.openWires.length :=
            Nat.lt_trans highBelowPosition windowBelowLength
          have highRead :
              natListGetAt (stepCapArc state position).openWires highPosition
                = natListGetAt state.openWires highPosition :=
            natListGetAt_natListRemoveTwoAt_below state.openWires position highPosition
              highBelowPosition
          have highValueBelow :
              natListGetAt state.openWires highPosition < state.nextFresh :=
            natListGetAt_lt_ofInRange state.nextFresh state.openWires highPosition
              highBelowLength fresh.1
          rw [lowRead, highRead,
            isSameComponent_stepCapArc_oldNodes state position fresh forest nfPos
              (natListGetAt state.openWires lowPosition)
              (natListGetAt state.openWires highPosition) lowValueBelow highValueBelow]
            at sameComponentHolds
          cases (isSameComponent_unionFindJoin_true_iff state.links forest
              (natListGetAt state.openWires position)
              (natListGetAt state.openWires (position + 1))
              (natListGetAt state.openWires lowPosition)
              (natListGetAt state.openWires highPosition)).mp sameComponentHolds with
          | inl alreadySame =>
              exact discipline lowPosition highPosition lowBelowHigh highBelowLength
                alreadySame
          | inr joinedPairings =>
              cases joinedPairings with
              | inl straightPairing =>
                  have highTiedToRight :
                      isSameComponent state.links
                          (natListGetAt state.openWires highPosition)
                          (natListGetAt state.openWires (position + 1)) = true :=
                    isSameComponent_true_symm state.links _ _ straightPairing.2
                  have windowSuccPinned :=
                    discipline highPosition (position + 1)
                      (Nat.lt_trans highBelowPosition (Nat.lt_succ_self position))
                      windowSuccBelowLength highTiedToRight
                  exact AdjunctionMode.noConfusion
                    (windowSuccPinned.2.symm.trans windowSuccParityIsBase)
              | inr crossedPairing =>
                  have lowTiedToRight :
                      isSameComponent state.links
                          (natListGetAt state.openWires lowPosition)
                          (natListGetAt state.openWires (position + 1)) = true :=
                    isSameComponent_true_symm state.links _ _ crossedPairing.2
                  have windowSuccPinned :=
                    discipline lowPosition (position + 1)
                      (Nat.lt_trans lowBelowPosition (Nat.lt_succ_self position))
                      windowSuccBelowLength lowTiedToRight
                  exact AdjunctionMode.noConfusion
                    (windowSuccPinned.2.symm.trans windowSuccParityIsBase)
      | inr positionLeHigh =>
          obtain ⟨highOffset, highOffsetEq⟩ := Nat.le.dest positionLeHigh
          subst highOffsetEq
          have highOldBelowLength :
              position + highOffset + 2 < state.openWires.length := by
            rw [← trimmedLengthPlusTwo]
            exact Nat.add_lt_add_right highBelowTrimmed 2
          have highRead :
              natListGetAt (stepCapArc state position).openWires (position + highOffset)
                = natListGetAt state.openWires (position + highOffset + 2) :=
            natListGetAt_natListRemoveTwoAt_pastPair state.openWires position highOffset
              windowInRange
          have highValueBelow :
              natListGetAt state.openWires (position + highOffset + 2)
                < state.nextFresh :=
            natListGetAt_lt_ofInRange state.nextFresh state.openWires
              (position + highOffset + 2) highOldBelowLength fresh.1
          rw [lowRead, highRead,
            isSameComponent_stepCapArc_oldNodes state position fresh forest nfPos
              (natListGetAt state.openWires lowPosition)
              (natListGetAt state.openWires (position + highOffset + 2))
              lowValueBelow highValueBelow] at sameComponentHolds
          cases (isSameComponent_unionFindJoin_true_iff state.links forest
              (natListGetAt state.openWires position)
              (natListGetAt state.openWires (position + 1))
              (natListGetAt state.openWires lowPosition)
              (natListGetAt state.openWires (position + highOffset + 2))).mp
              sameComponentHolds with
          | inl alreadySame =>
              have lowBelowHighOld : lowPosition < position + highOffset + 2 :=
                Nat.lt_trans lowBelowPosition
                  (Nat.lt_of_le_of_lt (Nat.le_add_right position highOffset)
                    (Nat.lt_add_of_pos_right (by decide)))
              obtain ⟨lowParity, highOldParity⟩ :=
                discipline lowPosition (position + highOffset + 2) lowBelowHighOld
                  highOldBelowLength alreadySame
              rw [adjunctionModeAtDistance_stableUnderTwoShift sourceMode
                (position + highOffset)] at highOldParity
              exact ⟨lowParity, highOldParity⟩
          | inr joinedPairings =>
              cases joinedPairings with
              | inl straightPairing =>
                  have lowTiedToLeft :
                      isSameComponent state.links
                          (natListGetAt state.openWires lowPosition)
                          (natListGetAt state.openWires position) = true :=
                    isSameComponent_true_symm state.links _ _ straightPairing.1
                  have lowPinned :=
                    discipline lowPosition position lowBelowPosition windowBelowLength
                      lowTiedToLeft
                  have windowSuccBelowHighOld :
                      position + 1 < position + highOffset + 2 :=
                    Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1))
                      (Nat.add_le_add_right (Nat.le_add_right position highOffset) 2)
                  obtain ⟨_, highOldParity⟩ :=
                    discipline (position + 1) (position + highOffset + 2)
                      windowSuccBelowHighOld highOldBelowLength straightPairing.2
                  rw [adjunctionModeAtDistance_stableUnderTwoShift sourceMode
                    (position + highOffset)] at highOldParity
                  exact ⟨lowPinned.1, highOldParity⟩
              | inr crossedPairing =>
                  have lowTiedToRight :
                      isSameComponent state.links
                          (natListGetAt state.openWires lowPosition)
                          (natListGetAt state.openWires (position + 1)) = true :=
                    isSameComponent_true_symm state.links _ _ crossedPairing.2
                  have windowSuccPinned :=
                    discipline lowPosition (position + 1)
                      (Nat.lt_trans lowBelowPosition (Nat.lt_succ_self position))
                      windowSuccBelowLength lowTiedToRight
                  exact AdjunctionMode.noConfusion
                    (windowSuccPinned.2.symm.trans windowSuccParityIsBase)
  | inr positionLeLow =>
      obtain ⟨lowOffset, lowOffsetEq⟩ := Nat.le.dest positionLeLow
      subst lowOffsetEq
      have positionLeHigh : position ≤ highPosition :=
        Nat.le_trans (Nat.le_add_right position lowOffset) (Nat.le_of_lt lowBelowHigh)
      obtain ⟨highOffset, highOffsetEq⟩ := Nat.le.dest positionLeHigh
      subst highOffsetEq
      have highOldBelowLength : position + highOffset + 2 < state.openWires.length := by
        rw [← trimmedLengthPlusTwo]
        exact Nat.add_lt_add_right highBelowTrimmed 2
      have lowOldBelowHighOld :
          position + lowOffset + 2 < position + highOffset + 2 :=
        Nat.add_lt_add_right lowBelowHigh 2
      have lowOldBelowLength : position + lowOffset + 2 < state.openWires.length :=
        Nat.lt_trans lowOldBelowHighOld highOldBelowLength
      have lowRead :
          natListGetAt (stepCapArc state position).openWires (position + lowOffset)
            = natListGetAt state.openWires (position + lowOffset + 2) :=
        natListGetAt_natListRemoveTwoAt_pastPair state.openWires position lowOffset
          windowInRange
      have highRead :
          natListGetAt (stepCapArc state position).openWires (position + highOffset)
            = natListGetAt state.openWires (position + highOffset + 2) :=
        natListGetAt_natListRemoveTwoAt_pastPair state.openWires position highOffset
          windowInRange
      have lowValueBelow :
          natListGetAt state.openWires (position + lowOffset + 2) < state.nextFresh :=
        natListGetAt_lt_ofInRange state.nextFresh state.openWires
          (position + lowOffset + 2) lowOldBelowLength fresh.1
      have highValueBelow :
          natListGetAt state.openWires (position + highOffset + 2) < state.nextFresh :=
        natListGetAt_lt_ofInRange state.nextFresh state.openWires
          (position + highOffset + 2) highOldBelowLength fresh.1
      have windowBelowLowOld : position < position + lowOffset + 2 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right position lowOffset)
          (Nat.lt_add_of_pos_right (by decide))
      have windowBelowHighOld : position < position + highOffset + 2 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right position highOffset)
          (Nat.lt_add_of_pos_right (by decide))
      rw [lowRead, highRead,
        isSameComponent_stepCapArc_oldNodes state position fresh forest nfPos
          (natListGetAt state.openWires (position + lowOffset + 2))
          (natListGetAt state.openWires (position + highOffset + 2))
          lowValueBelow highValueBelow] at sameComponentHolds
      cases (isSameComponent_unionFindJoin_true_iff state.links forest
          (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1))
          (natListGetAt state.openWires (position + lowOffset + 2))
          (natListGetAt state.openWires (position + highOffset + 2))).mp
          sameComponentHolds with
      | inl alreadySame =>
          obtain ⟨lowOldParity, highOldParity⟩ :=
            discipline (position + lowOffset + 2) (position + highOffset + 2)
              lowOldBelowHighOld highOldBelowLength alreadySame
          rw [adjunctionModeAtDistance_stableUnderTwoShift sourceMode
            (position + lowOffset)] at lowOldParity
          rw [adjunctionModeAtDistance_stableUnderTwoShift sourceMode
            (position + highOffset)] at highOldParity
          exact ⟨lowOldParity, highOldParity⟩
      | inr joinedPairings =>
          cases joinedPairings with
          | inl straightPairing =>
              have windowPinned :=
                discipline position (position + lowOffset + 2) windowBelowLowOld
                  lowOldBelowLength straightPairing.1
              exact AdjunctionMode.noConfusion
                (windowParityIsTip.symm.trans windowPinned.1)
          | inr crossedPairing =>
              have windowPinned :=
                discipline position (position + highOffset + 2) windowBelowHighOld
                  highOldBelowLength crossedPairing.1
              exact AdjunctionMode.noConfusion
                (windowParityIsTip.symm.trans windowPinned.1)

/-! ## Honesty marker -/

/-- **Honesty marker — the CAP preservation of the typed-ends discipline is SHIPPED (peel
campaign C, rung 2c).**  `arcOpenEndsDiscipline_stepCapArc`: a cap fired in range at a
`tip`-parity window carries `ArcOpenEndsDiscipline` across `stepCapArc`, via the merged-links
transfer (`isSameComponent_stepCapArc_oldNodes` over the cap root atlas), the join split
(`isSameComponent_unionFindJoin_true_iff`), and the forced-side analysis (left-tied wires
sit left at `base`, right-tied wires sit right at `tip`, crossed pairings refuted by order
through the window parities).  What this marker does NOT claim: the loop-freedom and
leg-separation consequences (rung 3 — though the same-component cap refutation is now one
discipline instance away) and the fold-level assembly threading `fresh`/`forest`/chained
window bounds through `processArcSpine`.  `= true`. -/
def fxMode_hasArcCapDisciplinePreservation : Bool := true

end FX1Poly.Polygraph
