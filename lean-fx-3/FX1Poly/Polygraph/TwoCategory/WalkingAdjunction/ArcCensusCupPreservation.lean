import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCapPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegSeparation

/-! # ArcCensusCupPreservation — a cup step preserves the boundary census (peel campaign H, cup rung 2d-iii)

A cup splices two fresh legs into the open wires and creates its own strand.  The token
accounting: the new strand carries exactly the two window slots (its legs' open ends), old
components keep their tokens through the splice reindexing, and no token crosses between the
worlds — the leg strand contains no old node.  Three same-component tokens after the step then
classify by node zone: any old/leg mixture is refuted by the leg separation, three leg tokens
pigeonhole into the two window slots against their distinctness, and three old tokens transport
through the cup's component transparency onto the old census via the splice backmap.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The splice backmap on boundary end tokens -/

/-- Is this stepped-state token OUTSIDE the cup's spliced window?  Bottom ports always are;
an open slot is outside when it sits strictly below the window or at-or-past its far edge —
exactly the tokens that survive from the old state. -/
def isCupOldZoneToken (position : Nat) : ArcEndToken → Prop
  | ArcEndToken.bottomPort _ => True
  | ArcEndToken.openSlot slotPosition => slotPosition < position ∨ position + 2 ≤ slotPosition

/-- Map an old-zone boundary end of the SPLICED state back to the old state: bottom ports are
untouched; a below-window slot keeps its position, an at-or-past-window slot came from two
positions lower.  (On the two window slots themselves the value is junk — every use is guarded
by `isCupOldZoneToken`.) -/
def cupEndTokenBackmap (position : Nat) : ArcEndToken → ArcEndToken
  | ArcEndToken.bottomPort portValue => ArcEndToken.bottomPort portValue
  | ArcEndToken.openSlot slotPosition =>
      ArcEndToken.openSlot (if slotPosition < position then slotPosition else slotPosition - 2)

/-- The splice backmap preserves the read node on the old zone: below-window reads are
untouched, past-window reads shift over the spliced pair. -/
theorem cupEndTokenBackmap_node (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) (token : ArcEndToken)
    (zone : isCupOldZoneToken position token) :
    arcEndTokenNode (stepCupArc state position) token
      = arcEndTokenNode state (cupEndTokenBackmap position token) := by
  cases token with
  | bottomPort portValue => rfl
  | openSlot slotPosition =>
      show natListGetAt (natListInsertAt state.openWires position
          [state.nextFresh, state.nextFresh + 1]) slotPosition
        = natListGetAt state.openWires
            (if slotPosition < position then slotPosition else slotPosition - 2)
      cases zone with
      | inl slotBelowWindow =>
          rw [if_pos slotBelowWindow]
          exact natListGetAt_natListInsertAt_below state.openWires position
            [state.nextFresh, state.nextFresh + 1] slotPosition slotBelowWindow
            (Nat.lt_of_lt_of_le slotBelowWindow cupInRange)
      | inr windowPastSlot =>
          obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastSlot
          have slotSpec : slotPosition = position + gapAmount + 2 :=
            gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
          have positionLeSlot : position ≤ slotPosition :=
            Nat.le_trans (Nat.le_add_right position 2) windowPastSlot
          have backmapValue : slotPosition - 2 = position + gapAmount := by
            rw [slotSpec]
            exact rfl
          have pastRead : natListGetAt (natListInsertAt state.openWires position
              [state.nextFresh, state.nextFresh + 1]) (position + gapAmount + 2)
              = natListGetAt state.openWires (position + gapAmount) :=
            natListGetAt_natListInsertAt_pastBlock state.openWires position
              [state.nextFresh, state.nextFresh + 1] gapAmount cupInRange
          rw [if_neg (fun slotBelowWindow =>
              Nat.lt_irrefl position (Nat.lt_of_le_of_lt positionLeSlot slotBelowWindow)),
            backmapValue, slotSpec]
          exact pastRead

/-- The splice backmap preserves token validity on the old zone. -/
theorem cupEndTokenBackmap_isValid (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (token : ArcEndToken) (zone : isCupOldZoneToken position token)
    (cupInRange : position ≤ state.openWires.length)
    (validNew : isValidArcEndToken seedBoundary (stepCupArc state position) token) :
    isValidArcEndToken seedBoundary state (cupEndTokenBackmap position token) := by
  cases token with
  | bottomPort portValue => exact validNew
  | openSlot slotPosition =>
      show (if slotPosition < position then slotPosition else slotPosition - 2)
        < state.openWires.length
      cases zone with
      | inl slotBelowWindow =>
          rw [if_pos slotBelowWindow]
          exact Nat.lt_of_lt_of_le slotBelowWindow cupInRange
      | inr windowPastSlot =>
          obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastSlot
          have slotSpec : slotPosition = position + gapAmount + 2 :=
            gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
          have positionLeSlot : position ≤ slotPosition :=
            Nat.le_trans (Nat.le_add_right position 2) windowPastSlot
          have backmapValue : slotPosition - 2 = position + gapAmount := by
            rw [slotSpec]
            exact rfl
          have slotBelowNewLength : slotPosition < (natListInsertAt state.openWires position
              [state.nextFresh, state.nextFresh + 1]).length := validNew
          rw [natListInsertAt_length state.openWires position
            [state.nextFresh, state.nextFresh + 1]] at slotBelowNewLength
          rw [slotSpec] at slotBelowNewLength
          rw [if_neg (fun slotBelowWindow =>
              Nat.lt_irrefl position (Nat.lt_of_le_of_lt positionLeSlot slotBelowWindow)),
            backmapValue]
          exact Nat.lt_of_add_lt_add_right slotBelowNewLength

/-- The splice backmap is injective on the old zone: the below-window image stays below the
window and the past-window image lands at-or-past it, so the zones cannot collide, and each
zone's shift is injective. -/
theorem cupEndTokenBackmap_injective (position : Nat) (tokenOne tokenTwo : ArcEndToken)
    (zoneOne : isCupOldZoneToken position tokenOne)
    (zoneTwo : isCupOldZoneToken position tokenTwo)
    (backmapsEqual : cupEndTokenBackmap position tokenOne = cupEndTokenBackmap position tokenTwo) :
    tokenOne = tokenTwo := by
  cases tokenOne with
  | bottomPort valueOne =>
      cases tokenTwo with
      | bottomPort valueTwo =>
          injection backmapsEqual with valuesEqual
          exact congrArg ArcEndToken.bottomPort valuesEqual
      | openSlot slotTwo => exact ArcEndToken.noConfusion backmapsEqual
  | openSlot slotOne =>
      cases tokenTwo with
      | bottomPort valueTwo => exact ArcEndToken.noConfusion backmapsEqual
      | openSlot slotTwo =>
          injection backmapsEqual with shiftsEqual
          cases zoneOne with
          | inl oneBelowWindow =>
              rw [if_pos oneBelowWindow] at shiftsEqual
              cases zoneTwo with
              | inl twoBelowWindow =>
                  rw [if_pos twoBelowWindow] at shiftsEqual
                  exact congrArg ArcEndToken.openSlot shiftsEqual
              | inr windowPastTwo =>
                  obtain ⟨gapAmount, gapSpec⟩ := Nat.le.dest windowPastTwo
                  have slotSpec : slotTwo = position + gapAmount + 2 :=
                    gapSpec.symm.trans (Nat.add_right_comm position 2 gapAmount)
                  have positionLeTwo : position ≤ slotTwo :=
                    Nat.le_trans (Nat.le_add_right position 2) windowPastTwo
                  have backmapValue : slotTwo - 2 = position + gapAmount := by
                    rw [slotSpec]
                    exact rfl
                  rw [if_neg (fun twoBelowWindow =>
                      Nat.lt_irrefl position
                        (Nat.lt_of_le_of_lt positionLeTwo twoBelowWindow)),
                    backmapValue] at shiftsEqual
                  rw [shiftsEqual] at oneBelowWindow
                  exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_right position gapAmount)
                    oneBelowWindow) (Nat.lt_irrefl position)
          | inr windowPastOne =>
              obtain ⟨gapOne, gapOneSpec⟩ := Nat.le.dest windowPastOne
              have slotOneSpec : slotOne = position + gapOne + 2 :=
                gapOneSpec.symm.trans (Nat.add_right_comm position 2 gapOne)
              have positionLeOne : position ≤ slotOne :=
                Nat.le_trans (Nat.le_add_right position 2) windowPastOne
              have backmapValueOne : slotOne - 2 = position + gapOne := by
                rw [slotOneSpec]
                exact rfl
              rw [if_neg (fun oneBelowWindow =>
                  Nat.lt_irrefl position (Nat.lt_of_le_of_lt positionLeOne oneBelowWindow)),
                backmapValueOne] at shiftsEqual
              cases zoneTwo with
              | inl twoBelowWindow =>
                  rw [if_pos twoBelowWindow] at shiftsEqual
                  rw [← shiftsEqual] at twoBelowWindow
                  exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_right position gapOne)
                    twoBelowWindow) (Nat.lt_irrefl position)
              | inr windowPastTwo =>
                  obtain ⟨gapTwo, gapTwoSpec⟩ := Nat.le.dest windowPastTwo
                  have slotTwoSpec : slotTwo = position + gapTwo + 2 :=
                    gapTwoSpec.symm.trans (Nat.add_right_comm position 2 gapTwo)
                  have positionLeTwo : position ≤ slotTwo :=
                    Nat.le_trans (Nat.le_add_right position 2) windowPastTwo
                  have backmapValueTwo : slotTwo - 2 = position + gapTwo := by
                    rw [slotTwoSpec]
                    exact rfl
                  rw [if_neg (fun twoBelowWindow =>
                      Nat.lt_irrefl position
                        (Nat.lt_of_le_of_lt positionLeTwo twoBelowWindow)),
                    backmapValueTwo] at shiftsEqual
                  -- shiftsEqual : position + gapOne = position + gapTwo
                  have slotsEqual : slotOne = slotTwo := by
                    rw [slotOneSpec, slotTwoSpec,
                      congrArg (fun tail => tail + 2) shiftsEqual]
                  exact congrArg ArcEndToken.openSlot slotsEqual

/-! ## The cup preservation -/

/-- ★ **A CUP step preserves the boundary census.**  Classify the three offending tokens by
node zone: any old/leg mixture contradicts the leg separation, three leg tokens pigeonhole
into the two window slots against their pairwise distinctness, and three old-zone tokens
transport through the cup's component transparency onto the old census via the splice
backmap. -/
theorem arcBoundaryCensus_stepCupArc (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (oldCensus : ArcBoundaryCensus seedBoundary state) :
    ArcBoundaryCensus seedBoundary (stepCupArc state position) := by
  intro tokenOne tokenTwo tokenThree validOne validTwo validThree
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
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
          cases classify tokenThree validThree with
          | inl oldThree =>
              obtain ⟨zoneThree, nodeThreeBelow⟩ := oldThree
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
              have oldSameOneThree : isSameComponent state.links
                  (arcEndTokenNode state (cupEndTokenBackmap position tokenOne))
                  (arcEndTokenNode state (cupEndTokenBackmap position tokenThree)) = true := by
                rw [← cupEndTokenBackmap_node state position cupInRange tokenOne zoneOne,
                  ← cupEndTokenBackmap_node state position cupInRange tokenThree zoneThree,
                  ← isSameComponent_stepCupArc_oldProbes state position fresh forest
                    (arcEndTokenNode (stepCupArc state position) tokenOne)
                    (arcEndTokenNode (stepCupArc state position) tokenThree)
                    nodeOneBelow nodeThreeBelow]
                exact sameOneThree
              exact oldCensus (cupEndTokenBackmap position tokenOne)
                (cupEndTokenBackmap position tokenTwo) (cupEndTokenBackmap position tokenThree)
                (cupEndTokenBackmap_isValid seedBoundary state position tokenOne zoneOne
                  cupInRange validOne)
                (cupEndTokenBackmap_isValid seedBoundary state position tokenTwo zoneTwo
                  cupInRange validTwo)
                (cupEndTokenBackmap_isValid seedBoundary state position tokenThree zoneThree
                  cupInRange validThree)
                (fun backmapsEqual => oneNeTwo (cupEndTokenBackmap_injective position tokenOne
                  tokenTwo zoneOne zoneTwo backmapsEqual))
                (fun backmapsEqual => oneNeThree (cupEndTokenBackmap_injective position tokenOne
                  tokenThree zoneOne zoneThree backmapsEqual))
                (fun backmapsEqual => twoNeThree (cupEndTokenBackmap_injective position tokenTwo
                  tokenThree zoneTwo zoneThree backmapsEqual))
                oldSameOneTwo oldSameOneThree
          | inr legThree =>
              exact refuteOldLeg (arcEndTokenNode (stepCupArc state position) tokenOne)
                (arcEndTokenNode (stepCupArc state position) tokenThree) nodeOneBelow
                (legNodeAtLeast tokenThree legThree) sameOneThree
      | inr legTwo =>
          exact refuteOldLeg (arcEndTokenNode (stepCupArc state position) tokenOne)
            (arcEndTokenNode (stepCupArc state position) tokenTwo) nodeOneBelow
            (legNodeAtLeast tokenTwo legTwo) sameOneTwo
  | inr legOne =>
      cases classify tokenTwo validTwo with
      | inl oldTwo =>
          exact refuteLegOld (arcEndTokenNode (stepCupArc state position) tokenOne)
            (arcEndTokenNode (stepCupArc state position) tokenTwo)
            (legNodeAtLeast tokenOne legOne) oldTwo.2 sameOneTwo
      | inr legTwo =>
          cases classify tokenThree validThree with
          | inl oldThree =>
              exact refuteLegOld (arcEndTokenNode (stepCupArc state position) tokenOne)
                (arcEndTokenNode (stepCupArc state position) tokenThree)
                (legNodeAtLeast tokenOne legOne) oldThree.2 sameOneThree
          | inr legThree =>
              cases legOne with
              | inl oneIsLeft =>
                  cases legTwo with
                  | inl twoIsLeft => exact oneNeTwo (oneIsLeft.1.trans twoIsLeft.1.symm)
                  | inr twoIsRight =>
                      cases legThree with
                      | inl threeIsLeft =>
                          exact oneNeThree (oneIsLeft.1.trans threeIsLeft.1.symm)
                      | inr threeIsRight =>
                          exact twoNeThree (twoIsRight.1.trans threeIsRight.1.symm)
              | inr oneIsRight =>
                  cases legTwo with
                  | inl twoIsLeft =>
                      cases legThree with
                      | inl threeIsLeft =>
                          exact twoNeThree (twoIsLeft.1.trans threeIsLeft.1.symm)
                      | inr threeIsRight =>
                          exact oneNeThree (oneIsRight.1.trans threeIsRight.1.symm)
                  | inr twoIsRight => exact oneNeTwo (oneIsRight.1.trans twoIsRight.1.symm)

/-- **Honesty marker — the CUP census preservation is SHIPPED (peel campaign H, cup rung
2d-iii).**  The splice backmap on the old zone (node/validity-preserving, injective), the leg
reads, the three-way node classification, and the full old/leg dispatch: an in-range cup step
carries the two-endpoint boundary census forward.  What this marker does NOT claim: the fold
transport to the folded states (rung 2d-iv) and the rewired partner values it feeds (rung
2d-v).  `= true`. -/
def fxMode_hasArcCensusCupPreservation : Bool := true

end FX1Poly.Polygraph
