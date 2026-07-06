import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPositions
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # ArcNonCrossingCupPreservation — stepCupArc preserves ArcNonCrossing (cup rung D2a-iii)

The main preservation theorem's first ingredient: a boundary end token of the spliced state is
either an OLD-ZONE read (union-find node strictly below `nextFresh`, so invisible to the fresh cup
component) or one of the two new cup legs (`openSlot position` / `openSlot (position+1)`).  This is
the classification that lets the crossing argument split every same-component arc into "both legs"
(an adjacent innermost cup — nothing can interleave) or "both old-zone" (backmaps to an old
crossing).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private read-membership plumbing (per-file copy, following the codebase pattern) -/

private theorem natListGetAt_mem_inRange : (wires : List Nat) → (index : Nat) →
    index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-! ## The token node classification -/

/-- ★ **A valid boundary token of the spliced state is old-zone or a new leg.**  Bottom ports and
below/past-window open slots read a wire strictly below `nextFresh`; the two window slots ARE the
freshly allocated cup legs. -/
theorem arcCupTokenNodeClass (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (token : ArcEndToken)
    (valid : isValidArcEndToken seedBoundary (stepCupArc state position) token) :
    arcEndTokenNode (stepCupArc state position) token < state.nextFresh
      ∨ token = ArcEndToken.openSlot position
      ∨ token = ArcEndToken.openSlot (position + 1) := by
  cases token with
  | bottomPort portValue =>
      exact Or.inl (Nat.lt_of_lt_of_le valid seedBelowFresh)
  | openSlot slot =>
      rcases Nat.lt_or_ge slot position with slotBelow | slotAtLeast
      · have slotBelowLen : slot < state.openWires.length :=
          Nat.lt_of_lt_of_le slotBelow cupInRange
        have readEq : arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot slot)
            = natListGetAt state.openWires slot :=
          natListGetAt_natListInsertAt_below state.openWires position
            [state.nextFresh, state.nextFresh + 1] slot slotBelow slotBelowLen
        exact Or.inl (by
          rw [readEq]
          exact fresh.1 (natListGetAt state.openWires slot)
            (natListGetAt_mem_inRange state.openWires slot slotBelowLen))
      · rcases Nat.lt_or_ge slot (position + 1) with slotAtPos | slotPastPos
        · have slotEqPos : slot = position :=
            Nat.le_antisymm (Nat.le_of_lt_succ slotAtPos) slotAtLeast
          exact Or.inr (Or.inl (by rw [slotEqPos]))
        · rcases Nat.lt_or_ge slot (position + 2) with slotAtPosOne | slotPast
          · have slotEqPosOne : slot = position + 1 :=
              Nat.le_antisymm (Nat.le_of_lt_succ slotAtPosOne) slotPastPos
            exact Or.inr (Or.inr (by rw [slotEqPosOne]))
          · obtain ⟨extra, extraEq⟩ := Nat.le.dest slotPast
            have slotForm : slot = position + extra + 2 := by
              rw [← extraEq, Nat.add_right_comm]
            have readEq : arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot slot)
                = natListGetAt state.openWires (position + extra) := by
              show natListGetAt (natListInsertAt state.openWires position
                  [state.nextFresh, state.nextFresh + 1]) slot
                = natListGetAt state.openWires (position + extra)
              rw [slotForm]
              exact natListGetAt_natListInsertAt_pastBlock state.openWires position
                [state.nextFresh, state.nextFresh + 1] extra cupInRange
            have validLen : slot < (stepCupArc state position).openWires.length := valid
            rw [arcCupNewOpenLength, slotForm] at validLen
            have posExtraLen : position + extra < state.openWires.length :=
              Nat.lt_of_add_lt_add_right validLen
            exact Or.inl (by
              rw [readEq]
              exact fresh.1 (natListGetAt state.openWires (position + extra))
                (natListGetAt_mem_inRange state.openWires (position + extra) posExtraLen))

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-step token node classification (cup rung D2a-iii, part 2).**
`arcCupTokenNodeClass`: every valid boundary token of the spliced state reads below `nextFresh`
(old-zone) or is one of the two window slots (the new cup legs).  What this marker does NOT claim:
the same-component leg/old-zone dichotomy assembled on top (via the shipped
`isSameComponent_stepCupArc_{oldProbes,freshOldProbes}` lemmas), the old-zone monotone
position-remap, and the stepCupArc preservation of `ArcNonCrossing` itself.  `= true`. -/
def fxMode_hasArcCupTokenNodeClass : Bool := true

end FX1Poly.Polygraph
