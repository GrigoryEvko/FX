import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryCensus
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshComponentInvisibility
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCensusCapPreservation — a cap step preserves the boundary census (peel campaign H, cup rung 2d-ii)

A cap consumes the two open ends at its window and fuses their components.  The token
accounting: the merged component loses one open token from EACH side (the consumed window
slots), so its boundary count is `(≤2 - 1) + (≤2 - 1) ≤ 2` — the census survives.  Concretely,
every boundary end of the stepped state maps back to a boundary end of the old state through
the window backmap (bottom ports fixed, open slots reindexed by `freshShiftAbove position 2`),
the backmap is injective, misses the two consumed window slots, and preserves nodes and
validity.  Three same-component tokens after the step then dispatch through the wire join's
flat disjunction: either all three were already together (the old census refutes them
directly), or two of them sit with a consumed window slot's component — and the old census
refutes THAT triple, because the backmap never produces the window tokens themselves.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The window backmap on boundary end tokens -/

/-- Map a boundary end token of the CAPPED state back to the old state: bottom ports are
untouched; a surviving open slot below the window keeps its position, one at-or-past the
window came from two positions higher. -/
def capEndTokenBackmap (position : Nat) : ArcEndToken → ArcEndToken
  | ArcEndToken.bottomPort portValue => ArcEndToken.bottomPort portValue
  | ArcEndToken.openSlot slotPosition =>
      ArcEndToken.openSlot (freshShiftAbove position 2 slotPosition)

/-- The backmap preserves the read node: the stepped state's boundary end sits on the same
union-find node as its old-state preimage (below-window reads are untouched, past-window reads
shift by the removed pair). -/
theorem capEndTokenBackmap_node (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) (token : ArcEndToken) :
    arcEndTokenNode (stepCapArc state position) token
      = arcEndTokenNode state (capEndTokenBackmap position token) := by
  cases token with
  | bottomPort portValue => rfl
  | openSlot slotPosition =>
      show natListGetAt (natListRemoveTwoAt state.openWires position) slotPosition
        = natListGetAt state.openWires (freshShiftAbove position 2 slotPosition)
      cases Nat.lt_or_ge slotPosition position with
      | inl slotBelowWindow =>
          rw [freshShiftAbove_ofNotLe position 2 slotPosition (fun windowLeSlot =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowWindow))]
          exact natListGetAt_natListRemoveTwoAt_below state.openWires position slotPosition
            slotBelowWindow
      | inr windowLeSlot =>
          rw [freshShiftAbove_ofLe position 2 slotPosition windowLeSlot]
          obtain ⟨offsetAmount, offsetSpec⟩ := Nat.le.dest windowLeSlot
          have pastRead := natListGetAt_natListRemoveTwoAt_pastPair state.openWires position
            offsetAmount capInRange
          rw [offsetSpec] at pastRead
          exact pastRead

/-- The backmap preserves token validity: a genuine boundary end of the capped state comes
from a genuine boundary end of the old state. -/
theorem capEndTokenBackmap_isValid (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) (token : ArcEndToken)
    (validNew : isValidArcEndToken seedBoundary (stepCapArc state position) token) :
    isValidArcEndToken seedBoundary state (capEndTokenBackmap position token) := by
  cases token with
  | bottomPort portValue => exact validNew
  | openSlot slotPosition =>
      have slotBelowNewLength :
          slotPosition < (natListRemoveTwoAt state.openWires position).length := validNew
      have lengthSplit :
          (natListRemoveTwoAt state.openWires position).length + 2 = state.openWires.length :=
        natListRemoveTwoAt_length state.openWires position capInRange
      show freshShiftAbove position 2 slotPosition < state.openWires.length
      cases Nat.lt_or_ge slotPosition position with
      | inl slotBelowWindow =>
          rw [freshShiftAbove_ofNotLe position 2 slotPosition (fun windowLeSlot =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowWindow))]
          exact Nat.lt_of_lt_of_le slotBelowNewLength
            (lengthSplit ▸ Nat.le_add_right
              (natListRemoveTwoAt state.openWires position).length 2)
      | inr windowLeSlot =>
          rw [freshShiftAbove_ofLe position 2 slotPosition windowLeSlot]
          exact lengthSplit ▸ Nat.add_lt_add_right slotBelowNewLength 2

/-- The backmap is injective: distinct stepped-state ends come from distinct old ends. -/
theorem capEndTokenBackmap_injective (position : Nat) (tokenOne tokenTwo : ArcEndToken)
    (backmapsEqual : capEndTokenBackmap position tokenOne = capEndTokenBackmap position tokenTwo) :
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
          cases Nat.lt_or_ge slotOne position with
          | inl oneBelowWindow =>
              rw [freshShiftAbove_ofNotLe position 2 slotOne (fun windowLeOne =>
                Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeOne oneBelowWindow))]
                at shiftsEqual
              cases Nat.lt_or_ge slotTwo position with
              | inl twoBelowWindow =>
                  rw [freshShiftAbove_ofNotLe position 2 slotTwo (fun windowLeTwo =>
                    Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeTwo twoBelowWindow))]
                    at shiftsEqual
                  exact congrArg ArcEndToken.openSlot shiftsEqual
              | inr windowLeTwo =>
                  rw [freshShiftAbove_ofLe position 2 slotTwo windowLeTwo] at shiftsEqual
                  have twoBelowOne : slotTwo < slotOne :=
                    shiftsEqual.symm ▸ Nat.lt_add_of_pos_right (by decide)
                  exact absurd
                    (Nat.lt_of_lt_of_le (Nat.lt_trans twoBelowOne oneBelowWindow) windowLeTwo)
                    (Nat.lt_irrefl slotTwo)
          | inr windowLeOne =>
              rw [freshShiftAbove_ofLe position 2 slotOne windowLeOne] at shiftsEqual
              cases Nat.lt_or_ge slotTwo position with
              | inl twoBelowWindow =>
                  rw [freshShiftAbove_ofNotLe position 2 slotTwo (fun windowLeTwo =>
                    Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeTwo twoBelowWindow))]
                    at shiftsEqual
                  have oneBelowTwo : slotOne < slotTwo :=
                    shiftsEqual ▸ Nat.lt_add_of_pos_right (by decide)
                  exact absurd
                    (Nat.lt_of_lt_of_le (Nat.lt_trans oneBelowTwo twoBelowWindow) windowLeOne)
                    (Nat.lt_irrefl slotOne)
              | inr windowLeTwo =>
                  rw [freshShiftAbove_ofLe position 2 slotTwo windowLeTwo] at shiftsEqual
                  exact congrArg ArcEndToken.openSlot (Nat.succ.inj (Nat.succ.inj shiftsEqual))

/-- The backmap never produces the LEFT consumed window slot. -/
theorem capEndTokenBackmap_missesLeftWindow (position : Nat) (token : ArcEndToken) :
    capEndTokenBackmap position token ≠ ArcEndToken.openSlot position := by
  cases token with
  | bottomPort portValue =>
      intro tokensEqual
      exact ArcEndToken.noConfusion tokensEqual
  | openSlot slotPosition =>
      intro tokensEqual
      injection tokensEqual with shiftEqualsWindow
      cases Nat.lt_or_ge slotPosition position with
      | inl slotBelowWindow =>
          rw [freshShiftAbove_ofNotLe position 2 slotPosition (fun windowLeSlot =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowWindow))]
            at shiftEqualsWindow
          rw [shiftEqualsWindow] at slotBelowWindow
          exact Nat.lt_irrefl position slotBelowWindow
      | inr windowLeSlot =>
          rw [freshShiftAbove_ofLe position 2 slotPosition windowLeSlot] at shiftEqualsWindow
          have slotBelowBump : slotPosition < slotPosition + 2 :=
            Nat.lt_add_of_pos_right (by decide)
          rw [shiftEqualsWindow] at slotBelowBump
          exact Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowBump)

/-- The backmap never produces the RIGHT consumed window slot. -/
theorem capEndTokenBackmap_missesRightWindow (position : Nat) (token : ArcEndToken) :
    capEndTokenBackmap position token ≠ ArcEndToken.openSlot (position + 1) := by
  cases token with
  | bottomPort portValue =>
      intro tokensEqual
      exact ArcEndToken.noConfusion tokensEqual
  | openSlot slotPosition =>
      intro tokensEqual
      injection tokensEqual with shiftEqualsWindow
      cases Nat.lt_or_ge slotPosition position with
      | inl slotBelowWindow =>
          rw [freshShiftAbove_ofNotLe position 2 slotPosition (fun windowLeSlot =>
            Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelowWindow))]
            at shiftEqualsWindow
          rw [shiftEqualsWindow] at slotBelowWindow
          exact Nat.lt_irrefl position (Nat.lt_of_succ_lt slotBelowWindow)
      | inr windowLeSlot =>
          rw [freshShiftAbove_ofLe position 2 slotPosition windowLeSlot] at shiftEqualsWindow
          have windowEqualsBump : slotPosition + 1 = position :=
            Nat.succ.inj shiftEqualsWindow
          rw [← windowEqualsBump] at windowLeSlot
          exact Nat.not_succ_le_self slotPosition windowLeSlot

/-! ## The join membership dispatch -/

/-- ★ Same-component membership after a join, DISPATCHED: either the probes were already
together, or each cross pairing holds — the flat-disjunction characterization surfaced as an
`Or` for downstream case analysis. -/
theorem sameComponent_unionFindJoin_dispatch (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight probeOne probeTwo : Nat)
    (inJoin : isSameComponent (unionFindJoin links joinLeft joinRight) probeOne probeTwo = true) :
    isSameComponent links probeOne probeTwo = true
      ∨ (isSameComponent links joinLeft probeOne = true
          ∧ isSameComponent links joinRight probeTwo = true)
      ∨ (isSameComponent links joinLeft probeTwo = true
          ∧ isSameComponent links probeOne joinRight = true) := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOne probeTwo] at inJoin
  cases baseTest : isSameComponent links probeOne probeTwo with
  | true => exact Or.inl rfl
  | false =>
      rw [baseTest] at inJoin
      cases leftOneTest : isSameComponent links joinLeft probeOne with
      | true =>
          cases rightTwoTest : isSameComponent links joinRight probeTwo with
          | true => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          | false =>
              rw [leftOneTest, rightTwoTest] at inJoin
              cases leftTwoTest : isSameComponent links joinLeft probeTwo with
              | true =>
                  cases oneRightTest : isSameComponent links probeOne joinRight with
                  | true => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
                  | false =>
                      rw [leftTwoTest, oneRightTest] at inJoin
                      exact Bool.noConfusion inJoin
              | false =>
                  rw [leftTwoTest] at inJoin
                  exact Bool.noConfusion inJoin
      | false =>
          rw [leftOneTest] at inJoin
          cases leftTwoTest : isSameComponent links joinLeft probeTwo with
          | true =>
              cases oneRightTest : isSameComponent links probeOne joinRight with
              | true => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
              | false =>
                  rw [leftTwoTest, oneRightTest] at inJoin
                  exact Bool.noConfusion inJoin
          | false =>
              rw [leftTwoTest] at inJoin
              exact Bool.noConfusion inJoin

/-! ## The cap preservation -/

/-- ★ **A CAP step preserves the boundary census.**  Backmap the three offending tokens to the
old state (nodes and validity preserved, distinctness preserved, the consumed window slots
never hit), peel the event join, and dispatch the wire join: every branch hands the old census
a genuine three-token violation — either the backmapped triple itself, or two backmapped
tokens together with a consumed window slot whose component they share. -/
theorem arcBoundaryCensus_stepCapArc (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (capInRange : position + 2 ≤ state.openWires.length)
    (oldCensus : ArcBoundaryCensus seedBoundary state) :
    ArcBoundaryCensus seedBoundary (stepCapArc state position) := by
  intro tokenOne tokenTwo tokenThree validOne validTwo validThree
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
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
  have validOldThree := capEndTokenBackmap_isValid seedBoundary state position capInRange
    tokenThree validThree
  have oldOneNeTwo : capEndTokenBackmap position tokenOne ≠ capEndTokenBackmap position tokenTwo :=
    fun backmapsEqual => oneNeTwo (capEndTokenBackmap_injective position tokenOne tokenTwo
      backmapsEqual)
  have oldOneNeThree :
      capEndTokenBackmap position tokenOne ≠ capEndTokenBackmap position tokenThree :=
    fun backmapsEqual => oneNeThree (capEndTokenBackmap_injective position tokenOne tokenThree
      backmapsEqual)
  have oldTwoNeThree :
      capEndTokenBackmap position tokenTwo ≠ capEndTokenBackmap position tokenThree :=
    fun backmapsEqual => twoNeThree (capEndTokenBackmap_injective position tokenTwo tokenThree
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
  have joinedOneThree :
      isSameComponent
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
        (arcEndTokenNode state (capEndTokenBackmap position tokenThree)) = true := by
    rw [← isSameComponent_stepCapArc_oldProbes state position fresh forest
        (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
        (arcEndTokenNode state (capEndTokenBackmap position tokenThree))
        (nodeBelow (capEndTokenBackmap position tokenOne) validOldOne)
        (nodeBelow (capEndTokenBackmap position tokenThree) validOldThree),
      ← capEndTokenBackmap_node state position capInRange tokenOne,
      ← capEndTokenBackmap_node state position capInRange tokenThree]
    exact sameOneThree
  have dispatchOneTwo := sameComponent_unionFindJoin_dispatch state.links forest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
    (arcEndTokenNode state (capEndTokenBackmap position tokenTwo)) joinedOneTwo
  have dispatchOneThree := sameComponent_unionFindJoin_dispatch state.links forest
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
    (arcEndTokenNode state (capEndTokenBackmap position tokenThree)) joinedOneThree
  cases dispatchOneTwo with
  | inl baseOneTwo =>
      cases dispatchOneThree with
      | inl baseOneThree =>
          exact oldCensus (capEndTokenBackmap position tokenOne)
            (capEndTokenBackmap position tokenTwo) (capEndTokenBackmap position tokenThree)
            validOldOne validOldTwo validOldThree oldOneNeTwo oldOneNeThree oldTwoNeThree
            baseOneTwo baseOneThree
      | inr crossOneThree =>
          cases crossOneThree with
          | inl legOneThree =>
              obtain ⟨leftReachesOne, _rightReachesThree⟩ := legOneThree
              have leftReachesTwo := isSameComponent_trans state.links
                (natListGetAt state.openWires position)
                (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                (arcEndTokenNode state (capEndTokenBackmap position tokenTwo))
                leftReachesOne baseOneTwo
              exact oldCensus (ArcEndToken.openSlot position)
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenTwo)
                capLeftValid validOldOne validOldTwo
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenTwo))
                oldOneNeTwo leftReachesOne leftReachesTwo
          | inr swapOneThree =>
              obtain ⟨_leftReachesThree, oneReachesRight⟩ := swapOneThree
              have rightReachesOne := isSameComponent_flip state.links
                (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                (natListGetAt state.openWires (position + 1)) oneReachesRight
              have rightReachesTwo := isSameComponent_trans state.links
                (natListGetAt state.openWires (position + 1))
                (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                (arcEndTokenNode state (capEndTokenBackmap position tokenTwo))
                rightReachesOne baseOneTwo
              exact oldCensus (ArcEndToken.openSlot (position + 1))
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenTwo)
                capRightValid validOldOne validOldTwo
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenTwo))
                oldOneNeTwo rightReachesOne rightReachesTwo
  | inr crossOneTwo =>
      cases crossOneTwo with
      | inl legOneTwo =>
          obtain ⟨leftReachesOne, rightReachesTwo⟩ := legOneTwo
          cases dispatchOneThree with
          | inl baseOneThree =>
              have leftReachesThree := isSameComponent_trans state.links
                (natListGetAt state.openWires position)
                (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                (arcEndTokenNode state (capEndTokenBackmap position tokenThree))
                leftReachesOne baseOneThree
              exact oldCensus (ArcEndToken.openSlot position)
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenThree)
                capLeftValid validOldOne validOldThree
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenThree))
                oldOneNeThree leftReachesOne leftReachesThree
          | inr crossOneThree =>
              cases crossOneThree with
              | inl legOneThree =>
                  obtain ⟨_leftReachesOneAgain, rightReachesThree⟩ := legOneThree
                  exact oldCensus (ArcEndToken.openSlot (position + 1))
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    capRightValid validOldTwo validOldThree
                    (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenTwo))
                    (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenThree))
                    oldTwoNeThree rightReachesTwo rightReachesThree
              | inr swapOneThree =>
                  obtain ⟨leftReachesThree, oneReachesRight⟩ := swapOneThree
                  have baseOneTwo := isSameComponent_trans state.links
                    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires (position + 1))
                    (arcEndTokenNode state (capEndTokenBackmap position tokenTwo))
                    oneReachesRight rightReachesTwo
                  have oneReachesLeft := isSameComponent_flip state.links
                    (natListGetAt state.openWires position)
                    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                    leftReachesOne
                  have baseOneThree := isSameComponent_trans state.links
                    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires position)
                    (arcEndTokenNode state (capEndTokenBackmap position tokenThree))
                    oneReachesLeft leftReachesThree
                  exact oldCensus (capEndTokenBackmap position tokenOne)
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    validOldOne validOldTwo validOldThree oldOneNeTwo oldOneNeThree
                    oldTwoNeThree baseOneTwo baseOneThree
      | inr swapOneTwo =>
          obtain ⟨leftReachesTwo, oneReachesRight⟩ := swapOneTwo
          have rightReachesOne := isSameComponent_flip state.links
            (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
            (natListGetAt state.openWires (position + 1)) oneReachesRight
          cases dispatchOneThree with
          | inl baseOneThree =>
              have rightReachesThree := isSameComponent_trans state.links
                (natListGetAt state.openWires (position + 1))
                (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                (arcEndTokenNode state (capEndTokenBackmap position tokenThree))
                rightReachesOne baseOneThree
              exact oldCensus (ArcEndToken.openSlot (position + 1))
                (capEndTokenBackmap position tokenOne) (capEndTokenBackmap position tokenThree)
                capRightValid validOldOne validOldThree
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenOne))
                (Ne.symm (capEndTokenBackmap_missesRightWindow position tokenThree))
                oldOneNeThree rightReachesOne rightReachesThree
          | inr crossOneThree =>
              cases crossOneThree with
              | inl legOneThree =>
                  obtain ⟨leftReachesOne, rightReachesThree⟩ := legOneThree
                  have oneReachesLeft := isSameComponent_flip state.links
                    (natListGetAt state.openWires position)
                    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                    leftReachesOne
                  have baseOneTwo := isSameComponent_trans state.links
                    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires position)
                    (arcEndTokenNode state (capEndTokenBackmap position tokenTwo))
                    oneReachesLeft leftReachesTwo
                  have baseOneThree := isSameComponent_trans state.links
                    (arcEndTokenNode state (capEndTokenBackmap position tokenOne))
                    (natListGetAt state.openWires (position + 1))
                    (arcEndTokenNode state (capEndTokenBackmap position tokenThree))
                    oneReachesRight rightReachesThree
                  exact oldCensus (capEndTokenBackmap position tokenOne)
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    validOldOne validOldTwo validOldThree oldOneNeTwo oldOneNeThree
                    oldTwoNeThree baseOneTwo baseOneThree
              | inr swapOneThreeAgain =>
                  obtain ⟨leftReachesThree, _⟩ := swapOneThreeAgain
                  exact oldCensus (ArcEndToken.openSlot position)
                    (capEndTokenBackmap position tokenTwo)
                    (capEndTokenBackmap position tokenThree)
                    capLeftValid validOldTwo validOldThree
                    (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenTwo))
                    (Ne.symm (capEndTokenBackmap_missesLeftWindow position tokenThree))
                    oldTwoNeThree leftReachesTwo leftReachesThree

/-- **Honesty marker — the CAP census preservation is SHIPPED (peel campaign H, cup rung
2d-ii).**  The window backmap (node/validity-preserving, injective, missing both consumed
slots), the join membership dispatch, and the nine-branch preservation: an in-range cap step
carries the two-endpoint boundary census forward.  What this marker does NOT claim: the CUP
step preservation (rung 2d-iii) and the fold transport to the folded states (rung 2d-iv).
`= true`. -/
def fxMode_hasArcCensusCapPreservation : Bool := true

end FX1Poly.Polygraph
