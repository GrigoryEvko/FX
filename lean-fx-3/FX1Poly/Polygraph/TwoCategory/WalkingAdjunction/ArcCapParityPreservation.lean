import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCapPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEndTokenParity
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcOpenEndsDiscipline

/-! # ArcCapParityPreservation — a cap step preserves the opposite-class invariant (peel campaign H, parity rung P-3)

A cap consumes the two open ends at its window and fuses their components.  The class
accounting: the two consumed window slots sit at adjacent positions, so their classes are
opposite BY CONSTRUCTION — and each surviving token of the merged strand is opposite to
its own side's consumed slot by the old invariant, so the two survivors land on opposite
classes again.  Concretely: backmap both tokens through the window backmap (class-stable —
surviving slots shift by two at most, and parity is two-shift stable), peel the event
join, and dispatch the wire join: the already-together branch is the old invariant
directly, and each leg-pairing branch chains the old invariant through the consumed slots'
definitionally-opposite classes.  No window-parity premise, and no separation premise —
the invariant survives even a loop-forming cap.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Class stability under the window backmap -/

/-- **The window backmap preserves the token class**: bottom ports are untouched,
below-window slots keep their position, and an at-or-past-window slot shifts by two —
parity is two-shift stable. -/
theorem arcEndTokenClass_capBackmap (sourceMode : AdjunctionMode) (position : Nat)
    (token : ArcEndToken) :
    arcEndTokenClass sourceMode (capEndTokenBackmap position token)
      = arcEndTokenClass sourceMode token := by
  cases token with
  | bottomPort portValue => rfl
  | openSlot slotPosition =>
      show adjunctionOppositeMode (adjunctionModeAtDistance sourceMode
          (freshShiftAbove position 2 slotPosition))
        = adjunctionOppositeMode (adjunctionModeAtDistance sourceMode slotPosition)
      cases Nat.lt_or_ge slotPosition position with
      | inl slotBelowWindow =>
          rw [freshShiftAbove_ofNotLe position 2 slotPosition (fun windowLeSlot =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowWindow))]
      | inr windowLeSlot =>
          rw [freshShiftAbove_ofLe position 2 slotPosition windowLeSlot]
          exact congrArg adjunctionOppositeMode
            (adjunctionModeAtDistance_stableUnderTwoShift sourceMode slotPosition)

/-! ## The opposite-class flip -/

/-- Reading an opposite-class equation from the other side: if the left class is the flip
of the right, the right is the flip of the left. -/
private theorem oppositeClass_ofFlipped (leftClass rightClass : AdjunctionMode)
    (flipEq : leftClass = adjunctionOppositeMode rightClass) :
    rightClass = adjunctionOppositeMode leftClass := by
  rw [flipEq, adjunctionOppositeMode_isInvolutive rightClass]

/-! ## The cap preservation -/

/-- ★ **A CAP step preserves the opposite-class invariant.**  Backmap the two offending
tokens (classes preserved, distinctness preserved, the consumed window slots never hit),
peel the event join, and dispatch the wire join: the already-together branch is the old
invariant on the backmapped pair, and each leg-pairing branch chains the old invariant
through the consumed window slots, whose classes are opposite by construction.  No
window-parity premise and no separation premise — a loop-forming cap preserves the
invariant too. -/
theorem arcEndTokenParity_stepCapArc (sourceMode : AdjunctionMode) (seedBoundary : Nat)
    (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (capInRange : position + 2 ≤ state.openWires.length)
    (oldParity : ArcEndTokenParity sourceMode seedBoundary state) :
    ArcEndTokenParity sourceMode seedBoundary (stepCapArc state position) := by
  intro tokenOne tokenTwo validOne validTwo oneNeTwo sameOneTwo
  have boundPositive : 0 < state.nextFresh := by
    cases wiresShape : state.openWires with
    | nil =>
        rw [wiresShape] at capInRange
        exact absurd capInRange (Nat.not_succ_le_zero (position + 1))
    | cons headWire restWires =>
        have headInOpen : headWire ∈ state.openWires := by
          rw [wiresShape]
          exact List.Mem.head _
        exact Nat.lt_of_le_of_lt (Nat.zero_le headWire) (fresh.1 headWire headInOpen)
  have nodeBelow : ∀ token : ArcEndToken, isValidArcEndToken seedBoundary state token →
      arcEndTokenNode state token < state.nextFresh := by
    intro token tokenValid
    cases token with
    | bottomPort portValue => exact Nat.lt_of_lt_of_le tokenValid seedBelowFresh
    | openSlot slotPosition =>
        exact natListGetAt_lt state.nextFresh boundPositive state.openWires slotPosition fresh.1
  have validOldOne := capEndTokenBackmap_isValid seedBoundary state position capInRange
    tokenOne validOne
  have validOldTwo := capEndTokenBackmap_isValid seedBoundary state position capInRange
    tokenTwo validTwo
  have oldOneNeTwo :
      capEndTokenBackmap position tokenOne ≠ capEndTokenBackmap position tokenTwo :=
    fun backmapsEqual => oneNeTwo (capEndTokenBackmap_injective position tokenOne tokenTwo
      backmapsEqual)
  have capLeftValid : isValidArcEndToken seedBoundary state (ArcEndToken.openSlot position) :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) capInRange
  have capRightValid :
      isValidArcEndToken seedBoundary state (ArcEndToken.openSlot (position + 1)) :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) position) capInRange
  have joinedOneTwo :
      isSameComponent
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
        (arcEndTokenNode state (capEndTokenBackmap position tokenTwo)) = true := by
    rw [← isSameComponent_stepCapArc_oldProbes state position fresh forest
        (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
        (arcEndTokenNode state (capEndTokenBackmap position tokenTwo))
        (nodeBelow (capEndTokenBackmap position tokenOne) validOldOne)
        (nodeBelow (capEndTokenBackmap position tokenTwo) validOldTwo),
      ← capEndTokenBackmap_node state position capInRange tokenOne,
      ← capEndTokenBackmap_node state position capInRange tokenTwo]
    exact sameOneTwo
  have dispatchOneTwo := sameComponent_unionFindJoin_dispatch state.links forest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
    (arcEndTokenNode state (capEndTokenBackmap position tokenTwo)) joinedOneTwo
  rw [← arcEndTokenClass_capBackmap sourceMode position tokenOne,
    ← arcEndTokenClass_capBackmap sourceMode position tokenTwo]
  cases dispatchOneTwo with
  | inl baseOneTwo =>
      exact oldParity (capEndTokenBackmap position tokenOne)
        (capEndTokenBackmap position tokenTwo) validOldOne validOldTwo oldOneNeTwo baseOneTwo
  | inr crossOneTwo =>
      cases crossOneTwo with
      | inl legOneTwo =>
          obtain ⟨leftReachesOne, rightReachesTwo⟩ := legOneTwo
          have windowLeftClassEq := oldParity (ArcEndToken.openSlot position)
            (capEndTokenBackmap position tokenOne) capLeftValid validOldOne
            (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenOne)) leftReachesOne
          have windowRightClassEq := oldParity (ArcEndToken.openSlot (position + 1))
            (capEndTokenBackmap position tokenTwo) capRightValid validOldTwo
            (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenTwo)) rightReachesTwo
          have firstFromWindow := oppositeClass_ofFlipped
            (arcEndTokenClass sourceMode (ArcEndToken.openSlot position))
            (arcEndTokenClass sourceMode (capEndTokenBackmap position tokenOne))
            windowLeftClassEq
          have secondFromWindow := oppositeClass_ofFlipped
            (arcEndTokenClass sourceMode (ArcEndToken.openSlot (position + 1)))
            (arcEndTokenClass sourceMode (capEndTokenBackmap position tokenTwo))
            windowRightClassEq
          have flippedSecond := ((congrArg adjunctionOppositeMode secondFromWindow).trans
            (adjunctionOppositeMode_isInvolutive
              (arcEndTokenClass sourceMode (ArcEndToken.openSlot (position + 1))))).symm
          exact firstFromWindow.trans flippedSecond
      | inr swapOneTwo =>
          obtain ⟨leftReachesTwo, oneReachesRight⟩ := swapOneTwo
          have rightReachesOne := isSameComponent_flip state.links
            (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
            (natListGetAt state.openWires (position + 1)) oneReachesRight
          have windowRightClassEq := oldParity (ArcEndToken.openSlot (position + 1))
            (capEndTokenBackmap position tokenOne) capRightValid validOldOne
            (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenOne)) rightReachesOne
          have windowLeftClassEq := oldParity (ArcEndToken.openSlot position)
            (capEndTokenBackmap position tokenTwo) capLeftValid validOldTwo
            (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenTwo)) leftReachesTwo
          have firstFromWindow := oppositeClass_ofFlipped
            (arcEndTokenClass sourceMode (ArcEndToken.openSlot (position + 1)))
            (arcEndTokenClass sourceMode (capEndTokenBackmap position tokenOne))
            windowRightClassEq
          have secondFromWindow := oppositeClass_ofFlipped
            (arcEndTokenClass sourceMode (ArcEndToken.openSlot position))
            (arcEndTokenClass sourceMode (capEndTokenBackmap position tokenTwo))
            windowLeftClassEq
          have firstNormalized := firstFromWindow.trans
            (adjunctionOppositeMode_isInvolutive
              (arcEndTokenClass sourceMode (ArcEndToken.openSlot position)))
          have flippedSecond := ((congrArg adjunctionOppositeMode secondFromWindow).trans
            (adjunctionOppositeMode_isInvolutive
              (arcEndTokenClass sourceMode (ArcEndToken.openSlot position)))).symm
          exact firstNormalized.trans flippedSecond

/-! ## Honesty marker -/

/-- **Honesty marker — the CAP parity preservation is SHIPPED (peel campaign H, parity
rung P-3).**  The class-stable window backmap (`arcEndTokenClass_capBackmap`) and the join
dispatch (`arcEndTokenParity_stepCapArc`): an in-range cap step carries the opposite-class
strand-endpoint invariant forward — the merged strand's survivors chain through the
consumed window slots' definitionally-opposite classes, with no window-parity and no
separation premise.  What this marker does NOT claim: the fold transport to chained spines
(rung P-4) and the cup partner-matching cancel (rung P-5).  `= true`. -/
def fxMode_hasArcCapParityPreservation : Bool := true

end FX1Poly.Polygraph
