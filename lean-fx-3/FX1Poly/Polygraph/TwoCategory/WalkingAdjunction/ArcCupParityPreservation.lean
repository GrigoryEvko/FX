import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEndTokenParity
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcOpenEndsDiscipline

/-! # ArcCupParityPreservation — a cup step preserves the opposite-class invariant (peel campaign H, parity rung P-2)

A cup splices two fresh legs into the open wires and creates its own strand.  The class
accounting: the new strand's two tokens are the window slots at adjacent positions, and
adjacent slot classes are opposite BY CONSTRUCTION (the slot class flips the position
parity, and the parity alternates) — so the cup case needs NO window-parity premise.  Old
tokens keep their classes through the splice backmap (below-window slots keep their
position, past-window slots shift by two and parity is two-shift stable), old components
are transparent to the fresh joins, and old/leg mixtures are refuted by the leg
separation.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Class stability under the splice backmap -/

/-- **The splice backmap preserves the token class on the old zone**: bottom ports are
untouched, below-window slots keep their position, and a past-window slot shifts by two —
parity is two-shift stable. -/
theorem arcEndTokenClass_cupBackmap (sourceMode : AdjunctionMode) (position : Nat)
    (token : ArcEndToken) (zone : isCupOldZoneToken position token) :
    arcEndTokenClass sourceMode (cupEndTokenBackmap position token)
      = arcEndTokenClass sourceMode token := by
  cases token with
  | bottomPort portValue => rfl
  | openSlot slotPosition =>
      show adjunctionOppositeMode (adjunctionModeAtDistance sourceMode
          (if slotPosition < position then slotPosition else slotPosition - 2))
        = adjunctionOppositeMode (adjunctionModeAtDistance sourceMode slotPosition)
      cases zone with
      | inl slotBelowWindow => rw [if_pos slotBelowWindow]
      | inr windowPastSlot =>
          obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastSlot
          have slotSpec : slotPosition = position + gapAmount + 2 :=
            gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
          have positionLeSlot : position ≤ slotPosition :=
            Nat.le_trans (Nat.le_add_right position 2) windowPastSlot
          have backmapValue : slotPosition - 2 = position + gapAmount := by
            rw [slotSpec]
            exact rfl
          rw [if_neg (fun slotBelowWindow =>
              Nat.lt_irrefl position (Nat.lt_of_le_of_lt positionLeSlot slotBelowWindow)),
            backmapValue, slotSpec]
          exact congrArg adjunctionOppositeMode
            (adjunctionModeAtDistance_stableUnderTwoShift sourceMode
              (position + gapAmount)).symm

/-! ## The cup preservation -/

/-- ★ **A CUP step preserves the opposite-class invariant.**  Classify the two offending
tokens by node zone: old/leg mixtures contradict the leg separation, two leg tokens are
the adjacent window slots whose classes are opposite by construction (no window-parity
premise needed), and two old-zone tokens transport through the cup's component
transparency onto the old invariant via the class-stable splice backmap. -/
theorem arcEndTokenParity_stepCupArc (sourceMode : AdjunctionMode) (seedBoundary : Nat)
    (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (oldParity : ArcEndTokenParity sourceMode seedBoundary state) :
    ArcEndTokenParity sourceMode seedBoundary (stepCupArc state position) := by
  intro tokenOne tokenTwo validOne validTwo oneNeTwo sameOneTwo
  have wireReadBelowFresh : ∀ index : Nat, index < state.openWires.length →
      natListGetAt state.openWires index < state.nextFresh := by
    intro index indexBelowLength
    have boundPositive : 0 < state.nextFresh := by
      cases wiresShape : state.openWires with
      | nil =>
          rw [wiresShape] at indexBelowLength
          exact absurd indexBelowLength (Nat.not_lt_zero index)
      | cons headWire restWires =>
          have headInOpen : headWire ∈ state.openWires := by
            rw [wiresShape]
            exact List.Mem.head _
          exact Nat.lt_of_le_of_lt (Nat.zero_le headWire) (fresh.1 headWire headInOpen)
    exact natListGetAt_lt state.nextFresh boundPositive state.openWires index fresh.1
  have legReadLeft : natListGetAt (natListInsertAt state.openWires position
      [state.nextFresh, state.nextFresh + 1]) position = state.nextFresh := by
    have insideRead := natListGetAt_natListInsertAt_inside state.openWires position
      [state.nextFresh, state.nextFresh + 1] 0 (Nat.zero_lt_succ 1) cupInRange
    rw [Nat.add_zero] at insideRead
    exact insideRead
  have legReadRight : natListGetAt (natListInsertAt state.openWires position
      [state.nextFresh, state.nextFresh + 1]) (position + 1) = state.nextFresh + 1 :=
    natListGetAt_natListInsertAt_inside state.openWires position
      [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) cupInRange
  have classify : ∀ token : ArcEndToken,
      isValidArcEndToken seedBoundary (stepCupArc state position) token →
      (isCupOldZoneToken position token
          ∧ arcEndTokenNode (stepCupArc state position) token < state.nextFresh)
        ∨ (token = ArcEndToken.openSlot position
            ∧ arcEndTokenNode (stepCupArc state position) token = state.nextFresh)
        ∨ (token = ArcEndToken.openSlot (position + 1)
            ∧ arcEndTokenNode (stepCupArc state position) token = state.nextFresh + 1) := by
    intro token tokenValid
    cases token with
    | bottomPort portValue =>
        exact Or.inl ⟨True.intro, Nat.lt_of_lt_of_le tokenValid seedBelowFresh⟩
    | openSlot slotPosition =>
        cases Nat.lt_or_ge slotPosition position with
        | inl slotBelowWindow =>
            refine Or.inl ⟨Or.inl slotBelowWindow, ?_⟩
            show natListGetAt (natListInsertAt state.openWires position
                [state.nextFresh, state.nextFresh + 1]) slotPosition < state.nextFresh
            rw [natListGetAt_natListInsertAt_below state.openWires position
              [state.nextFresh, state.nextFresh + 1] slotPosition slotBelowWindow
              (Nat.lt_of_lt_of_le slotBelowWindow cupInRange)]
            exact wireReadBelowFresh slotPosition
              (Nat.lt_of_lt_of_le slotBelowWindow cupInRange)
        | inr windowLeSlot =>
            cases Nat.lt_or_ge slotPosition (position + 2) with
            | inl slotInWindow =>
                cases Nat.lt_or_ge slotPosition (position + 1) with
                | inl slotBelowSucc =>
                    have slotEqualsWindow : slotPosition = position :=
                      Nat.le_antisymm (Nat.le_of_lt_succ slotBelowSucc) windowLeSlot
                    refine Or.inr (Or.inl
                      ⟨congrArg ArcEndToken.openSlot slotEqualsWindow, ?_⟩)
                    show natListGetAt (natListInsertAt state.openWires position
                        [state.nextFresh, state.nextFresh + 1]) slotPosition = state.nextFresh
                    rw [slotEqualsWindow]
                    exact legReadLeft
                | inr succLeSlot =>
                    have slotEqualsSucc : slotPosition = position + 1 :=
                      Nat.le_antisymm (Nat.le_of_lt_succ slotInWindow) succLeSlot
                    refine Or.inr (Or.inr
                      ⟨congrArg ArcEndToken.openSlot slotEqualsSucc, ?_⟩)
                    show natListGetAt (natListInsertAt state.openWires position
                        [state.nextFresh, state.nextFresh + 1]) slotPosition
                      = state.nextFresh + 1
                    rw [slotEqualsSucc]
                    exact legReadRight
            | inr windowPastSlot =>
                refine Or.inl ⟨Or.inr windowPastSlot, ?_⟩
                obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastSlot
                have slotSpec : slotPosition = position + gapAmount + 2 :=
                  gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
                have pastRead : natListGetAt (natListInsertAt state.openWires position
                    [state.nextFresh, state.nextFresh + 1]) (position + gapAmount + 2)
                    = natListGetAt state.openWires (position + gapAmount) :=
                  natListGetAt_natListInsertAt_pastBlock state.openWires position
                    [state.nextFresh, state.nextFresh + 1] gapAmount cupInRange
                have slotBelowNewLength : slotPosition < (natListInsertAt state.openWires
                    position [state.nextFresh, state.nextFresh + 1]).length := tokenValid
                rw [natListInsertAt_length state.openWires position
                    [state.nextFresh, state.nextFresh + 1],
                  slotSpec] at slotBelowNewLength
                show natListGetAt (natListInsertAt state.openWires position
                    [state.nextFresh, state.nextFresh + 1]) slotPosition < state.nextFresh
                rw [slotSpec, pastRead]
                exact wireReadBelowFresh (position + gapAmount)
                  (Nat.lt_of_add_lt_add_right slotBelowNewLength)
  have refuteOldLeg : ∀ oldNode legNode : Nat, oldNode < state.nextFresh →
      state.nextFresh ≤ legNode →
      isSameComponent (stepCupArc state position).links oldNode legNode = true → False := by
    intro oldNode legNode oldBelow legAtLeast sameHolds
    rw [isSameComponent_stepCupArc_oldFreshProbes state position fresh forest oldNode legNode
      oldBelow legAtLeast] at sameHolds
    exact Bool.noConfusion sameHolds
  have refuteLegOld : ∀ legNode oldNode : Nat, state.nextFresh ≤ legNode →
      oldNode < state.nextFresh →
      isSameComponent (stepCupArc state position).links legNode oldNode = true → False := by
    intro legNode oldNode legAtLeast oldBelow sameHolds
    rw [isSameComponent_stepCupArc_freshOldProbes state position fresh forest legNode oldNode
      legAtLeast oldBelow] at sameHolds
    exact Bool.noConfusion sameHolds
  have legNodeAtLeast : ∀ token : ArcEndToken,
      (token = ArcEndToken.openSlot position
          ∧ arcEndTokenNode (stepCupArc state position) token = state.nextFresh)
        ∨ (token = ArcEndToken.openSlot (position + 1)
            ∧ arcEndTokenNode (stepCupArc state position) token = state.nextFresh + 1) →
      state.nextFresh ≤ arcEndTokenNode (stepCupArc state position) token := by
    intro token legFact
    cases legFact with
    | inl leftLeg => exact Nat.le_of_eq leftLeg.2.symm
    | inr rightLeg =>
        exact Nat.le_trans (Nat.le_succ state.nextFresh) (Nat.le_of_eq rightLeg.2.symm)
  cases classify tokenOne validOne with
  | inl oldOne =>
      obtain ⟨zoneOne, nodeOneBelow⟩ := oldOne
      cases classify tokenTwo validTwo with
      | inl oldTwo =>
          obtain ⟨zoneTwo, nodeTwoBelow⟩ := oldTwo
          have oldSameOneTwo : isSameComponent state.links
              (arcEndTokenNode state (cupEndTokenBackmap position tokenOne))
              (arcEndTokenNode state (cupEndTokenBackmap position tokenTwo)) = true := by
            rw [← cupEndTokenBackmap_node state position cupInRange tokenOne zoneOne,
              ← cupEndTokenBackmap_node state position cupInRange tokenTwo zoneTwo,
              ← isSameComponent_stepCupArc_oldProbes state position fresh forest
                (arcEndTokenNode (stepCupArc state position) tokenOne)
                (arcEndTokenNode (stepCupArc state position) tokenTwo)
                nodeOneBelow nodeTwoBelow]
            exact sameOneTwo
          have backmapParity := oldParity (cupEndTokenBackmap position tokenOne)
            (cupEndTokenBackmap position tokenTwo)
            (cupEndTokenBackmap_isValid seedBoundary state position tokenOne zoneOne
              cupInRange validOne)
            (cupEndTokenBackmap_isValid seedBoundary state position tokenTwo zoneTwo
              cupInRange validTwo)
            (fun backmapsEqual => oneNeTwo (cupEndTokenBackmap_injective position tokenOne
              tokenTwo zoneOne zoneTwo backmapsEqual))
            oldSameOneTwo
          rw [arcEndTokenClass_cupBackmap sourceMode position tokenOne zoneOne,
            arcEndTokenClass_cupBackmap sourceMode position tokenTwo zoneTwo]
            at backmapParity
          exact backmapParity
      | inr legTwo =>
          exact False.elim (refuteOldLeg
            (arcEndTokenNode (stepCupArc state position) tokenOne)
            (arcEndTokenNode (stepCupArc state position) tokenTwo) nodeOneBelow
            (legNodeAtLeast tokenTwo legTwo) sameOneTwo)
  | inr legOne =>
      cases classify tokenTwo validTwo with
      | inl oldTwo =>
          exact False.elim (refuteLegOld
            (arcEndTokenNode (stepCupArc state position) tokenOne)
            (arcEndTokenNode (stepCupArc state position) tokenTwo)
            (legNodeAtLeast tokenOne legOne) oldTwo.2 sameOneTwo)
      | inr legTwo =>
          cases legOne with
          | inl oneIsLeft =>
              cases legTwo with
              | inl twoIsLeft => exact absurd (oneIsLeft.1.trans twoIsLeft.1.symm) oneNeTwo
              | inr twoIsRight =>
                  rw [oneIsLeft.1, twoIsRight.1]
                  show adjunctionOppositeMode (adjunctionModeAtDistance sourceMode position)
                    = adjunctionOppositeMode (adjunctionOppositeMode
                        (adjunctionModeAtDistance sourceMode (position + 1)))
                  rw [adjunctionOppositeMode_isInvolutive
                    (adjunctionModeAtDistance sourceMode (position + 1))]
                  exact rfl
          | inr oneIsRight =>
              cases legTwo with
              | inl twoIsLeft =>
                  rw [oneIsRight.1, twoIsLeft.1]
                  exact rfl
              | inr twoIsRight =>
                  exact absurd (oneIsRight.1.trans twoIsRight.1.symm) oneNeTwo

/-! ## Honesty marker -/

/-- **Honesty marker — the CUP parity preservation is SHIPPED (peel campaign H, parity
rung P-2).**  The class-stable splice backmap (`arcEndTokenClass_cupBackmap`) and the full
old/leg dispatch (`arcEndTokenParity_stepCupArc`): an in-range cup step carries the
opposite-class strand-endpoint invariant forward, with NO window-parity premise — adjacent
slot classes are opposite by construction.  What this marker does NOT claim: the cap step
preservation (rung P-3 — the strand merge across a consuming join), the fold transport to
chained spines (rung P-4), and the cup partner-matching cancel (rung P-5).  `= true`. -/
def fxMode_hasArcCupParityPreservation : Bool := true

end FX1Poly.Polygraph
