import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingInvariant
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCapPreservation

/-! # ArcNonCrossingCapPreservation — the cap-step position infrastructure (cap rung D2a-iv, part 1)

The dual of the cup: a cap CONSUMES the two open ends at its window (`stepCapArc` removes them
via `natListRemoveTwoAt` and fuses their components with a fresh event node).  Unlike the cup —
whose two legs formed a fresh isolated component — the cap JOINS two old components, so the
same-component transfer is NOT transparent and the main preservation must peel the wire join.
This file ships the position side, which IS a clean dual of the cup: the consumed frontier is
two shorter, every surviving boundary token reads an old wire strictly below `nextFresh`, the two
window slots sit at ADJACENT cyclic positions, and the window backmap (`freshShiftAbove position
2`) is strictly monotone, so the backmapped tokens' old positions strictly increase whenever the
spliced positions do.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private clean Nat-subtraction plumbing (Init's cancel/pos lemmas leak propext) -/

/-- `(start + amount) - start = amount`, hand-rolled clean. -/
private theorem addSubCancelLeft : (start amount : Nat) → (start + amount) - start = amount
  | 0, amount => by rw [Nat.zero_add, Nat.sub_zero]
  | start + 1, amount => by
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact addSubCancelLeft start amount

/-- A subtraction from a strictly larger minuend is positive, hand-rolled clean. -/
private theorem subPosOfLt (position bound : Nat) (posLt : position < bound) :
    0 < bound - position := by
  obtain ⟨diff, diffEq⟩ := Nat.le.dest posLt
  have reshape : position + 1 + diff = position + (diff + 1) := by
    rw [Nat.add_right_comm, Nat.add_assoc]
  rw [← diffEq, reshape, addSubCancelLeft]
  exact Nat.succ_pos diff

/-- `minuend - (position + 1) + 1 = minuend - position` on the valid range, hand-rolled clean. -/
private theorem subSuccAddOne (minuend position : Nat) (posLt : position < minuend) :
    minuend - (position + 1) + 1 = minuend - position := by
  rw [Nat.sub_succ]
  exact Nat.succ_pred_eq_of_pos (subPosOfLt position minuend posLt)

/-- Non-strict antitone: `smaller ≤ larger → minuend - larger ≤ minuend - smaller`. -/
private theorem subMonotoneLe (minuend smaller larger : Nat) (order : smaller ≤ larger) :
    minuend - larger ≤ minuend - smaller := by
  obtain ⟨gap, gapEq⟩ := Nat.le.dest order
  rw [← gapEq]
  clear gapEq order
  induction gap with
  | zero => rw [Nat.add_zero]; exact Nat.le_refl _
  | succ gapPred inductiveHypothesis =>
      rw [Nat.add_succ, Nat.sub_succ]
      exact Nat.le_trans (Nat.pred_le (minuend - (smaller + gapPred))) inductiveHypothesis

/-- Strict antitone on the valid range: `smaller < larger ≤ minuend → minuend - larger < minuend
- smaller`. -/
private theorem subStrictAntitone (minuend smaller larger : Nat)
    (order : smaller < larger) (largerLe : larger ≤ minuend) :
    minuend - larger < minuend - smaller := by
  obtain ⟨rest, restEq⟩ := Nat.le.dest largerLe
  obtain ⟨diff, diffEq⟩ := Nat.le.dest (Nat.le_of_lt order)
  have diffPos : 0 < diff := Nat.pos_of_ne_zero (fun diffZero => by
    rw [diffZero, Nat.add_zero] at diffEq
    exact Nat.lt_irrefl smaller (diffEq.symm ▸ order))
  have lowSide : minuend - larger = rest := by
    rw [← restEq]; exact addSubCancelLeft larger rest
  have highSide : minuend - smaller = diff + rest := by
    have expand : minuend = smaller + (diff + rest) := by
      rw [← restEq, ← diffEq, Nat.add_assoc]
    rw [expand]; exact addSubCancelLeft smaller (diff + rest)
  rw [lowSide, highSide, Nat.add_comm diff rest]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rest) (Nat.add_le_add_left diffPos rest)

/-- `index < bound → index ≤ bound - 1`, hand-rolled clean. -/
private theorem ltImpliesLePred : (index bound : Nat) → index < bound → index ≤ bound - 1
  | _, 0, indexLt => absurd indexLt (Nat.not_lt_zero _)
  | _, _ + 1, indexLt => Nat.le_of_lt_succ indexLt

/-- The cap window backmap `freshShiftAbove position 2` is strictly monotone on slot indices:
below-window slots keep their index, at-or-past-window slots shift up by two, both order-preserving
(and a below/past pair can never invert since below `< position ≤` past). -/
private theorem freshShiftAboveTwoMonotone (position slotSmaller slotLarger : Nat)
    (slotOrder : slotSmaller < slotLarger) :
    freshShiftAbove position 2 slotSmaller < freshShiftAbove position 2 slotLarger := by
  rcases Nat.lt_or_ge slotSmaller position with smallerBelow | smallerAtLeast
  · rw [freshShiftAbove_ofNotLe position 2 slotSmaller
      (fun windowLeSmaller => Nat.lt_irrefl position
        (Nat.lt_of_le_of_lt windowLeSmaller smallerBelow))]
    rcases Nat.lt_or_ge slotLarger position with largerBelow | largerAtLeast
    · rw [freshShiftAbove_ofNotLe position 2 slotLarger
        (fun windowLeLarger => Nat.lt_irrefl position
          (Nat.lt_of_le_of_lt windowLeLarger largerBelow))]
      exact slotOrder
    · rw [freshShiftAbove_ofLe position 2 slotLarger largerAtLeast]
      exact Nat.lt_of_lt_of_le smallerBelow
        (Nat.le_trans largerAtLeast (Nat.le_add_right slotLarger 2))
  · rw [freshShiftAbove_ofLe position 2 slotSmaller smallerAtLeast,
      freshShiftAbove_ofLe position 2 slotLarger
        (Nat.le_trans smallerAtLeast (Nat.le_of_lt slotOrder))]
    exact Nat.add_lt_add_right slotOrder 2

/-! ## The spliced open-wire length and the window positions -/

/-- A fired cap consumes its two window ends, so the open-wire frontier shrinks by exactly two. -/
theorem arcCapNewOpenLength (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) :
    (stepCapArc state position).openWires.length + 2 = state.openWires.length :=
  natListRemoveTwoAt_length state.openWires position capInRange

/-- ★ **The two consumed cap window slots occupy adjacent cyclic positions** — `openSlot (position
+ 1)` is exactly one below `openSlot position` on the old boundary.  The cap consumes an innermost
nested adjacent pair, which is the dual of the cup's adjacent legs. -/
theorem arcCapWindowAdjacent (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) :
    arcEndTokenPosition seedBoundary state (ArcEndToken.openSlot (position + 1)) + 1
      = arcEndTokenPosition seedBoundary state (ArcEndToken.openSlot position) := by
  show seedBoundary + (state.openWires.length - 1 - (position + 1)) + 1
    = seedBoundary + (state.openWires.length - 1 - position)
  rw [Nat.add_assoc]
  have positionBelowPred : position < state.openWires.length - 1 :=
    ltImpliesLePred (position + 1) state.openWires.length capInRange
  rw [subSuccAddOne (state.openWires.length - 1) position positionBelowPred]

/-! ## Every surviving cap boundary token reads below nextFresh -/

/-- A surviving boundary end of the capped state reads a union-find node strictly below `nextFresh`
— bottom ports sit below the seed width, and every surviving open slot reads an old wire, which is
below `nextFresh` by freshness (the fresh event node is consumed into the links, never exposed as an
open end). -/
theorem arcCapNodeBelow (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (capInRange : position + 2 ≤ state.openWires.length) (token : ArcEndToken)
    (valid : isValidArcEndToken seedBoundary (stepCapArc state position) token) :
    arcEndTokenNode (stepCapArc state position) token < state.nextFresh := by
  have boundPositive : 0 < state.nextFresh := by
    cases wiresShape : state.openWires with
    | nil =>
        rw [wiresShape] at capInRange
        exact absurd capInRange (Nat.not_succ_le_zero (position + 1))
    | cons headWire restWires =>
        have headInOpen : headWire ∈ state.openWires := by
          rw [wiresShape]; exact List.Mem.head _
        exact Nat.lt_of_le_of_lt (Nat.zero_le headWire) (fresh.1 headWire headInOpen)
  cases token with
  | bottomPort portValue => exact Nat.lt_of_lt_of_le valid seedBelowFresh
  | openSlot slot =>
      rw [capEndTokenBackmap_node state position capInRange (ArcEndToken.openSlot slot)]
      exact natListGetAt_lt state.nextFresh boundPositive state.openWires
        (freshShiftAbove position 2 slot) fresh.1

/-! ## The cap old-position monotone remap -/

/-- ★ **The cap-window backmap is a strictly monotone position remap.**  For two surviving tokens
whose cyclic positions strictly increase in the capped state, the backmapped tokens' positions
strictly increase in the old state.  Bottom ports keep their sub-`seedBoundary` value; open slots
reverse past the seed block, and `freshShiftAbove position 2` preserves that order. -/
theorem arcCapOldPositionMonotone (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length)
    (tokenLow tokenHigh : ArcEndToken)
    (validLow : isValidArcEndToken seedBoundary (stepCapArc state position) tokenLow)
    (validHigh : isValidArcEndToken seedBoundary (stepCapArc state position) tokenHigh)
    (newPosLt : arcEndTokenPosition seedBoundary (stepCapArc state position) tokenLow
      < arcEndTokenPosition seedBoundary (stepCapArc state position) tokenHigh) :
    arcEndTokenPosition seedBoundary state (capEndTokenBackmap position tokenLow)
      < arcEndTokenPosition seedBoundary state (capEndTokenBackmap position tokenHigh) := by
  cases tokenLow with
  | bottomPort valueLow =>
      cases tokenHigh with
      | bottomPort valueHigh => exact newPosLt
      | openSlot slotHigh =>
          exact Nat.lt_of_lt_of_le validLow (Nat.le_add_right seedBoundary _)
  | openSlot slotLow =>
      cases tokenHigh with
      | bottomPort valueHigh =>
          exact absurd
            (Nat.lt_of_le_of_lt (Nat.le_add_right seedBoundary _)
              (Nat.lt_trans newPosLt validHigh))
            (Nat.lt_irrefl seedBoundary)
      | openSlot slotHigh =>
          have innerLt : (stepCapArc state position).openWires.length - 1 - slotLow
              < (stepCapArc state position).openWires.length - 1 - slotHigh :=
            Nat.lt_of_add_lt_add_left newPosLt
          have slotHighLtLow : slotHigh < slotLow := by
            rcases Nat.lt_or_ge slotHigh slotLow with below | atLeast
            · exact below
            · exact absurd (Nat.lt_of_lt_of_le innerLt
                (subMonotoneLe ((stepCapArc state position).openWires.length - 1)
                  slotLow slotHigh atLeast))
                (Nat.lt_irrefl _)
          have backLowValid : freshShiftAbove position 2 slotLow < state.openWires.length :=
            capEndTokenBackmap_isValid seedBoundary state position capInRange
              (ArcEndToken.openSlot slotLow) validLow
          show seedBoundary + (state.openWires.length - 1 - freshShiftAbove position 2 slotLow)
            < seedBoundary + (state.openWires.length - 1 - freshShiftAbove position 2 slotHigh)
          exact Nat.add_lt_add_left
            (subStrictAntitone (state.openWires.length - 1)
              (freshShiftAbove position 2 slotHigh) (freshShiftAbove position 2 slotLow)
              (freshShiftAboveTwoMonotone position slotHigh slotLow slotHighLtLow)
              (ltImpliesLePred _ state.openWires.length backLowValid))
            seedBoundary

/-! ## Every backmapped token lands off the two-slot window gap -/

/-- ★ **A surviving token's backmap sits strictly outside the consumed window gap.**  The two
consumed window slots occupy adjacent positions `Q < Q+1`; every backmapped boundary token lands
strictly below `Q` (bottom ports and past-window slots) or strictly above `Q+1` (below-window
slots), never at `Q` or `Q+1`.  Combined with a `≤` bound against a window position this forces the
matching strict `<`, the fact the INSIDE crossing branch of the main preservation needs. -/
theorem arcCapBackmapPositionOffWindow (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (capInRange : position + 2 ≤ state.openWires.length) (token : ArcEndToken)
    (valid : isValidArcEndToken seedBoundary (stepCapArc state position) token) :
    arcEndTokenPosition seedBoundary state (capEndTokenBackmap position token)
        < arcEndTokenPosition seedBoundary state (ArcEndToken.openSlot (position + 1))
      ∨ arcEndTokenPosition seedBoundary state (ArcEndToken.openSlot position)
        < arcEndTokenPosition seedBoundary state (capEndTokenBackmap position token) := by
  have positionBelowPred : position ≤ state.openWires.length - 1 :=
    Nat.le_trans (Nat.le_succ position)
      (ltImpliesLePred (position + 1) state.openWires.length capInRange)
  cases token with
  | bottomPort portValue =>
      exact Or.inl (Nat.lt_of_lt_of_le valid (Nat.le_add_right seedBoundary _))
  | openSlot slot =>
      have backValid : freshShiftAbove position 2 slot < state.openWires.length :=
        capEndTokenBackmap_isValid seedBoundary state position capInRange
          (ArcEndToken.openSlot slot) valid
      rcases Nat.lt_or_ge slot position with slotBelow | slotAtLeast
      · refine Or.inr ?_
        show seedBoundary + (state.openWires.length - 1 - position)
          < seedBoundary + (state.openWires.length - 1 - freshShiftAbove position 2 slot)
        rw [freshShiftAbove_ofNotLe position 2 slot
          (fun windowLeSlot => Nat.lt_irrefl position (Nat.lt_of_le_of_lt windowLeSlot slotBelow))]
        exact Nat.add_lt_add_left
          (subStrictAntitone (state.openWires.length - 1) slot position slotBelow positionBelowPred)
          seedBoundary
      · refine Or.inl ?_
        have slotBumpBelowLength : slot + 2 < state.openWires.length := by
          rw [← freshShiftAbove_ofLe position 2 slot slotAtLeast]; exact backValid
        show seedBoundary + (state.openWires.length - 1 - freshShiftAbove position 2 slot)
          < seedBoundary + (state.openWires.length - 1 - (position + 1))
        rw [freshShiftAbove_ofLe position 2 slot slotAtLeast]
        exact Nat.add_lt_add_left
          (subStrictAntitone (state.openWires.length - 1) (position + 1) (slot + 2)
            (Nat.lt_of_le_of_lt (Nat.add_le_add_right slotAtLeast 1) (Nat.lt_succ_self (slot + 1)))
            (ltImpliesLePred (slot + 2) state.openWires.length slotBumpBelowLength))
          seedBoundary

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-step position infrastructure (cap rung D2a-iv, part 1).**
`arcCapNewOpenLength` (the frontier shrinks by two), `arcCapWindowAdjacent` (the two consumed
window slots at adjacent cyclic positions — the innermost nested pair), `arcCapNodeBelow` (every
surviving token reads below `nextFresh`), and `arcCapOldPositionMonotone` (the window backmap is a
strictly monotone position remap), on a hand-rolled clean Nat-subtraction base.  What this marker
does NOT claim: the stepCapArc preservation of `ArcNonCrossing` itself (the main theorem — needs
the wire-join dispatch), the whole-spine fold, and the extract translation to `IsNonCrossing`.
`= true`. -/
def fxMode_hasArcNonCrossingCapPositions : Bool := true

end FX1Poly.Polygraph
