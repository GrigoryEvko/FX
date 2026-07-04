import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcOpenEndsDiscipline
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupRootAtlas
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # ArcCupDisciplinePreservation — the cup step preserves the typed-ends discipline (peel campaign C, rung 2b)

A cup fired at a `base`-parity window keeps the `ArcOpenEndsDiscipline` invariant: the two
fresh legs form their own component at positions `(window, window + 1)` — exactly
`(base, tip)` typed by the window-parity premise — while every old pair keeps its old
connectivity (the cup's joins touch only its fresh triple, `unionFindRootOf_stepCupArc_old`)
at parities stable under the two-position shift.  Fresh-leg-to-old-wire pairs are refuted
outright: the legs root at `nextFresh + 1`, old roots stay strictly below `nextFresh`.

The window-parity premise (`base` at the fire position) is discharged at the fold level by
`adjunctionCupAtom_windowPositionMode` — a cup atom of the walking adjunction can only fire
at a `base`-parity position.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Read and component plumbing over one cup step -/

/-- An in-range read from a list of all-below-bound wires stays below the bound — the
in-range companion of `natListGetAt_lt` (which instead needs `0 < bound` to cover the
past-the-end default read). -/
theorem natListGetAt_lt_ofInRange (bound : Nat) :
    (wires : List Nat) → (index : Nat) → index < wires.length →
    (∀ wire ∈ wires, wire < bound) → natListGetAt wires index < bound
  | [], index, indexBelow, _ => absurd indexBelow (Nat.not_lt_zero index)
  | headWire :: _, 0, _, allBelow => allBelow headWire (List.Mem.head _)
  | _ :: restWires, index + 1, indexBelow, allBelow =>
      natListGetAt_lt_ofInRange bound restWires index (Nat.lt_of_succ_lt_succ indexBelow)
        (fun wire wireInRest => allBelow wire (List.Mem.tail _ wireInRest))

/-- **Old nodes keep their connectivity through a cup** — both roots are untouched by the
cup's fresh-triple joins, so the same-component test is unchanged. -/
theorem isSameComponent_stepCupArc_oldNodes (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (firstNode secondNode : Nat)
    (firstBelow : firstNode < state.nextFresh) (secondBelow : secondNode < state.nextFresh) :
    isSameComponent (stepCupArc state position).links firstNode secondNode
      = isSameComponent state.links firstNode secondNode := by
  have firstRootBelow : unionFindRootOf state.links firstNode < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) firstNode firstBelow
  have secondRootBelow : unionFindRootOf state.links secondNode < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) secondNode secondBelow
  show (unionFindRootOf (stepCupArc state position).links firstNode
      == unionFindRootOf (stepCupArc state position).links secondNode)
    = (unionFindRootOf state.links firstNode == unionFindRootOf state.links secondNode)
  rw [unionFindRootOf_stepCupArc_old state position fresh forest firstNode firstRootBelow,
    unionFindRootOf_stepCupArc_old state position fresh forest secondNode secondRootBelow]

/-- **An old wire is never in a cup leg's component** (old node on the LEFT).  The leg roots
at `nextFresh + 1`; the old node's root stays strictly below `nextFresh`. -/
theorem isSameComponent_stepCupArc_oldLeg_eq_false (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (oldNode legNode : Nat) (oldBelow : oldNode < state.nextFresh)
    (legRootsAtRightLeg :
      unionFindRootOf (stepCupArc state position).links legNode = state.nextFresh + 1) :
    isSameComponent (stepCupArc state position).links oldNode legNode = false := by
  have oldRootBelow : unionFindRootOf state.links oldNode < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) oldNode oldBelow
  show (unionFindRootOf (stepCupArc state position).links oldNode
      == unionFindRootOf (stepCupArc state position).links legNode) = false
  rw [unionFindRootOf_stepCupArc_old state position fresh forest oldNode oldRootBelow,
    legRootsAtRightLeg]
  exact beq_false_of_lt_left
    (Nat.lt_trans oldRootBelow (Nat.lt_succ_self state.nextFresh))

/-- **An old wire is never in a cup leg's component** (leg on the LEFT — the mirror). -/
theorem isSameComponent_stepCupArc_legOld_eq_false (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (legNode oldNode : Nat) (oldBelow : oldNode < state.nextFresh)
    (legRootsAtRightLeg :
      unionFindRootOf (stepCupArc state position).links legNode = state.nextFresh + 1) :
    isSameComponent (stepCupArc state position).links legNode oldNode = false := by
  have oldRootBelow : unionFindRootOf state.links oldNode < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2) oldNode oldBelow
  show (unionFindRootOf (stepCupArc state position).links legNode
      == unionFindRootOf (stepCupArc state position).links oldNode) = false
  rw [unionFindRootOf_stepCupArc_old state position fresh forest oldNode oldRootBelow,
    legRootsAtRightLeg]
  exact beq_false_of_lt (Nat.lt_trans oldRootBelow (Nat.lt_succ_self state.nextFresh))

/-! ## The preservation theorem -/

/-- ★ **A cup fired at a `base`-parity window preserves the typed-ends discipline.**  Case
split on where the two positions sit relative to the spliced two-leg block: below/below
transfers to the old discipline verbatim; leg/leg is the freshly-typed pair `(base, tip)` by
the window-parity premise; leg/old pairs are refuted by the root atlas; past-the-block
positions shift by two, where parity is stable. -/
theorem arcOpenEndsDiscipline_stepCupArc (sourceMode : AdjunctionMode)
    (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (positionInRange : position ≤ state.openWires.length)
    (windowParityIsBase :
      adjunctionModeAtDistance sourceMode position = AdjunctionMode.base)
    (discipline : ArcOpenEndsDiscipline sourceMode state) :
    ArcOpenEndsDiscipline sourceMode (stepCupArc state position) := by
  intro lowPosition highPosition lowBelowHigh highInRange sameComponentHolds
  have highBelowPadded : highPosition < state.openWires.length + 2 := by
    have highBelowInserted :
        highPosition
          < (natListInsertAt state.openWires position
              [state.nextFresh, state.nextFresh + 1]).length := highInRange
    rw [natListInsertAt_length state.openWires position
      [state.nextFresh, state.nextFresh + 1]] at highBelowInserted
    exact highBelowInserted
  cases Nat.lt_or_ge highPosition position with
  | inl highBelowPosition =>
      have lowBelowPosition : lowPosition < position :=
        Nat.lt_trans lowBelowHigh highBelowPosition
      have highBelowLength : highPosition < state.openWires.length :=
        Nat.lt_of_lt_of_le highBelowPosition positionInRange
      have lowBelowLength : lowPosition < state.openWires.length :=
        Nat.lt_trans lowBelowHigh highBelowLength
      have lowRead :
          natListGetAt (stepCupArc state position).openWires lowPosition
            = natListGetAt state.openWires lowPosition :=
        natListGetAt_natListInsertAt_below state.openWires position
          [state.nextFresh, state.nextFresh + 1] lowPosition lowBelowPosition lowBelowLength
      have highRead :
          natListGetAt (stepCupArc state position).openWires highPosition
            = natListGetAt state.openWires highPosition :=
        natListGetAt_natListInsertAt_below state.openWires position
          [state.nextFresh, state.nextFresh + 1] highPosition highBelowPosition
          highBelowLength
      have lowValueBelow : natListGetAt state.openWires lowPosition < state.nextFresh :=
        natListGetAt_lt_ofInRange state.nextFresh state.openWires lowPosition
          lowBelowLength fresh.1
      have highValueBelow : natListGetAt state.openWires highPosition < state.nextFresh :=
        natListGetAt_lt_ofInRange state.nextFresh state.openWires highPosition
          highBelowLength fresh.1
      rw [lowRead, highRead,
        isSameComponent_stepCupArc_oldNodes state position fresh forest
          (natListGetAt state.openWires lowPosition)
          (natListGetAt state.openWires highPosition) lowValueBelow highValueBelow]
        at sameComponentHolds
      exact discipline lowPosition highPosition lowBelowHigh highBelowLength
        sameComponentHolds
  | inr positionLeHigh =>
      cases Nat.eq_or_lt_of_le positionLeHigh with
      | inl positionEqHigh =>
          have lowBelowPosition : lowPosition < position := by
            rw [positionEqHigh]
            exact lowBelowHigh
          have lowBelowLength : lowPosition < state.openWires.length :=
            Nat.lt_of_lt_of_le lowBelowPosition positionInRange
          have lowRead :
              natListGetAt (stepCupArc state position).openWires lowPosition
                = natListGetAt state.openWires lowPosition :=
            natListGetAt_natListInsertAt_below state.openWires position
              [state.nextFresh, state.nextFresh + 1] lowPosition lowBelowPosition
              lowBelowLength
          have highRead :
              natListGetAt (stepCupArc state position).openWires highPosition
                = state.nextFresh := by
            rw [← positionEqHigh]
            exact natListGetAt_natListInsertAt_inside state.openWires position
              [state.nextFresh, state.nextFresh + 1] 0
              (Nat.succ_le_succ (Nat.zero_le 1)) positionInRange
          have lowValueBelow : natListGetAt state.openWires lowPosition < state.nextFresh :=
            natListGetAt_lt_ofInRange state.nextFresh state.openWires lowPosition
              lowBelowLength fresh.1
          rw [lowRead, highRead] at sameComponentHolds
          exact Bool.noConfusion
            ((isSameComponent_stepCupArc_oldLeg_eq_false state position fresh forest
                (natListGetAt state.openWires lowPosition) state.nextFresh lowValueBelow
                (stepCupArc_root_leftLeg state position fresh forest)).symm.trans
              sameComponentHolds)
      | inr positionLtHigh =>
          cases Nat.eq_or_lt_of_le (positionLtHigh : position + 1 ≤ highPosition) with
          | inl positionSuccEqHigh =>
              have positionOnePlusEqHigh : position + 1 = highPosition := positionSuccEqHigh
              cases Nat.lt_or_ge lowPosition position with
              | inl lowBelowPosition =>
                  have lowBelowLength : lowPosition < state.openWires.length :=
                    Nat.lt_of_lt_of_le lowBelowPosition positionInRange
                  have lowRead :
                      natListGetAt (stepCupArc state position).openWires lowPosition
                        = natListGetAt state.openWires lowPosition :=
                    natListGetAt_natListInsertAt_below state.openWires position
                      [state.nextFresh, state.nextFresh + 1] lowPosition lowBelowPosition
                      lowBelowLength
                  have highRead :
                      natListGetAt (stepCupArc state position).openWires highPosition
                        = state.nextFresh + 1 := by
                    rw [← positionOnePlusEqHigh]
                    exact natListGetAt_natListInsertAt_inside state.openWires position
                      [state.nextFresh, state.nextFresh + 1] 1 (Nat.le_refl 2)
                      positionInRange
                  have lowValueBelow :
                      natListGetAt state.openWires lowPosition < state.nextFresh :=
                    natListGetAt_lt_ofInRange state.nextFresh state.openWires lowPosition
                      lowBelowLength fresh.1
                  rw [lowRead, highRead] at sameComponentHolds
                  exact Bool.noConfusion
                    ((isSameComponent_stepCupArc_oldLeg_eq_false state position fresh forest
                        (natListGetAt state.openWires lowPosition) (state.nextFresh + 1)
                        lowValueBelow
                        (stepCupArc_root_rightLeg state position fresh forest)).symm.trans
                      sameComponentHolds)
              | inr positionLeLow =>
                  have lowBelowSucc : lowPosition < position + 1 := by
                    rw [positionOnePlusEqHigh]
                    exact lowBelowHigh
                  have lowEqPosition : lowPosition = position :=
                    Nat.le_antisymm (Nat.le_of_lt_succ lowBelowSucc) positionLeLow
                  refine ⟨?_, ?_⟩
                  · rw [lowEqPosition]
                    exact windowParityIsBase
                  · rw [← positionOnePlusEqHigh]
                    exact congrArg adjunctionOppositeMode windowParityIsBase
          | inr positionSuccLtHigh =>
              obtain ⟨highOffset, highOffsetEq⟩ :=
                Nat.le.dest (positionSuccLtHigh : position + 2 ≤ highPosition)
              have highEq : highPosition = position + highOffset + 2 :=
                highOffsetEq.symm.trans (Nat.add_right_comm position 2 highOffset)
              subst highEq
              have highInnerBelowLength :
                  position + highOffset < state.openWires.length :=
                Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ highBelowPadded)
              have highRead :
                  natListGetAt (stepCupArc state position).openWires
                      (position + highOffset + 2)
                    = natListGetAt state.openWires (position + highOffset) :=
                natListGetAt_natListInsertAt_pastBlock state.openWires position
                  [state.nextFresh, state.nextFresh + 1] highOffset positionInRange
              have highValueBelow :
                  natListGetAt state.openWires (position + highOffset) < state.nextFresh :=
                natListGetAt_lt_ofInRange state.nextFresh state.openWires
                  (position + highOffset) highInnerBelowLength fresh.1
              cases Nat.lt_or_ge lowPosition position with
              | inl lowBelowPosition =>
                  have lowBelowLength : lowPosition < state.openWires.length :=
                    Nat.lt_of_lt_of_le lowBelowPosition positionInRange
                  have lowRead :
                      natListGetAt (stepCupArc state position).openWires lowPosition
                        = natListGetAt state.openWires lowPosition :=
                    natListGetAt_natListInsertAt_below state.openWires position
                      [state.nextFresh, state.nextFresh + 1] lowPosition lowBelowPosition
                      lowBelowLength
                  have lowValueBelow :
                      natListGetAt state.openWires lowPosition < state.nextFresh :=
                    natListGetAt_lt_ofInRange state.nextFresh state.openWires lowPosition
                      lowBelowLength fresh.1
                  rw [lowRead, highRead,
                    isSameComponent_stepCupArc_oldNodes state position fresh forest
                      (natListGetAt state.openWires lowPosition)
                      (natListGetAt state.openWires (position + highOffset))
                      lowValueBelow highValueBelow] at sameComponentHolds
                  have lowBelowInner : lowPosition < position + highOffset :=
                    Nat.lt_of_lt_of_le lowBelowPosition (Nat.le_add_right position highOffset)
                  obtain ⟨lowParity, innerParity⟩ :=
                    discipline lowPosition (position + highOffset) lowBelowInner
                      highInnerBelowLength sameComponentHolds
                  refine ⟨lowParity, ?_⟩
                  rw [adjunctionModeAtDistance_stableUnderTwoShift sourceMode
                    (position + highOffset)]
                  exact innerParity
              | inr positionLeLow =>
                  cases Nat.eq_or_lt_of_le positionLeLow with
                  | inl positionEqLow =>
                      have lowRead :
                          natListGetAt (stepCupArc state position).openWires lowPosition
                            = state.nextFresh := by
                        rw [← positionEqLow]
                        exact natListGetAt_natListInsertAt_inside state.openWires position
                          [state.nextFresh, state.nextFresh + 1] 0
                          (Nat.succ_le_succ (Nat.zero_le 1)) positionInRange
                      rw [lowRead, highRead] at sameComponentHolds
                      exact Bool.noConfusion
                        ((isSameComponent_stepCupArc_legOld_eq_false state position fresh
                            forest state.nextFresh
                            (natListGetAt state.openWires (position + highOffset))
                            highValueBelow
                            (stepCupArc_root_leftLeg state position fresh forest)).symm.trans
                          sameComponentHolds)
                  | inr positionLtLow =>
                      cases Nat.eq_or_lt_of_le
                          (positionLtLow : position + 1 ≤ lowPosition) with
                      | inl positionSuccEqLow =>
                          have positionOnePlusEqLow : position + 1 = lowPosition :=
                            positionSuccEqLow
                          have lowRead :
                              natListGetAt (stepCupArc state position).openWires lowPosition
                                = state.nextFresh + 1 := by
                            rw [← positionOnePlusEqLow]
                            exact natListGetAt_natListInsertAt_inside state.openWires
                              position [state.nextFresh, state.nextFresh + 1] 1
                              (Nat.le_refl 2) positionInRange
                          rw [lowRead, highRead] at sameComponentHolds
                          exact Bool.noConfusion
                            ((isSameComponent_stepCupArc_legOld_eq_false state position
                                fresh forest (state.nextFresh + 1)
                                (natListGetAt state.openWires (position + highOffset))
                                highValueBelow
                                (stepCupArc_root_rightLeg state position fresh
                                  forest)).symm.trans
                              sameComponentHolds)
                      | inr positionSuccLtLow =>
                          obtain ⟨lowOffset, lowOffsetEq⟩ :=
                            Nat.le.dest (positionSuccLtLow : position + 2 ≤ lowPosition)
                          have lowEq : lowPosition = position + lowOffset + 2 :=
                            lowOffsetEq.symm.trans
                              (Nat.add_right_comm position 2 lowOffset)
                          subst lowEq
                          have innerBelowInner :
                              position + lowOffset < position + highOffset :=
                            Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ lowBelowHigh)
                          have lowInnerBelowLength :
                              position + lowOffset < state.openWires.length :=
                            Nat.lt_trans innerBelowInner highInnerBelowLength
                          have lowRead :
                              natListGetAt (stepCupArc state position).openWires
                                  (position + lowOffset + 2)
                                = natListGetAt state.openWires (position + lowOffset) :=
                            natListGetAt_natListInsertAt_pastBlock state.openWires position
                              [state.nextFresh, state.nextFresh + 1] lowOffset
                              positionInRange
                          have lowValueBelow :
                              natListGetAt state.openWires (position + lowOffset)
                                < state.nextFresh :=
                            natListGetAt_lt_ofInRange state.nextFresh state.openWires
                              (position + lowOffset) lowInnerBelowLength fresh.1
                          rw [lowRead, highRead,
                            isSameComponent_stepCupArc_oldNodes state position fresh forest
                              (natListGetAt state.openWires (position + lowOffset))
                              (natListGetAt state.openWires (position + highOffset))
                              lowValueBelow highValueBelow] at sameComponentHolds
                          obtain ⟨lowParity, highParity⟩ :=
                            discipline (position + lowOffset) (position + highOffset)
                              innerBelowInner highInnerBelowLength sameComponentHolds
                          refine ⟨?_, ?_⟩
                          · rw [adjunctionModeAtDistance_stableUnderTwoShift sourceMode
                              (position + lowOffset)]
                            exact lowParity
                          · rw [adjunctionModeAtDistance_stableUnderTwoShift sourceMode
                              (position + highOffset)]
                            exact highParity

/-! ## Honesty marker -/

/-- **Honesty marker — the CUP preservation of the typed-ends discipline is SHIPPED (peel
campaign C, rung 2b).**  `arcOpenEndsDiscipline_stepCupArc`: a cup fired in range at a
`base`-parity window carries `ArcOpenEndsDiscipline` across `stepCupArc`, via the old-node
component transfer (`isSameComponent_stepCupArc_oldNodes`), the two leg-vs-old refutations
(`isSameComponent_stepCupArc_oldLeg_eq_false` / `_legOld_eq_false`), the leg-pair typing
from the window-parity premise, and the two-shift parity stability.  What this marker does
NOT claim: the CAP preservation (rung 2c — the join transfer and the forced-side analysis)
and the loop-freedom / leg-separation consequences (rung 3).  `= true`. -/
def fxMode_hasArcCupDisciplinePreservation : Bool := true

end FX1Poly.Polygraph
