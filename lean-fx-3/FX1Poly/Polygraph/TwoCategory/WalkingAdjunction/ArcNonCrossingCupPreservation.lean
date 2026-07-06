import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPositions
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegSeparation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

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

/-! ## The two cup-leg node values -/

/-- The left cup leg (window slot `position`) reads the freshly allocated node `nextFresh`. -/
theorem arcCupLeftLegNode (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) :
    arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot position)
      = state.nextFresh :=
  natListGetAt_natListInsertAt_inside state.openWires position
    [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) cupInRange

/-- The right cup leg (window slot `position+1`) reads the freshly allocated node `nextFresh+1`. -/
theorem arcCupRightLegNode (state : ArcWireState) (position : Nat)
    (cupInRange : position ≤ state.openWires.length) :
    arcEndTokenNode (stepCupArc state position) (ArcEndToken.openSlot (position + 1))
      = state.nextFresh + 1 :=
  natListGetAt_natListInsertAt_inside state.openWires position
    [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) cupInRange

/-! ## The same-component dichotomy -/

/-- ★ **A same-component pair of spliced-state tokens is both old-zone or both cup legs.**  A leg
node roots in the fresh cup component, an old-zone node in an old component, and the two are never
joined (`isSameComponent_stepCupArc_{freshOld,oldFresh}Probes`) — so a same-component arc cannot
mix a leg with an old-zone token. -/
theorem arcCupSameComponentDichotomy (seedBoundary : Nat) (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (cupInRange : position ≤ state.openWires.length)
    (tokenLeft tokenRight : ArcEndToken)
    (validLeft : isValidArcEndToken seedBoundary (stepCupArc state position) tokenLeft)
    (validRight : isValidArcEndToken seedBoundary (stepCupArc state position) tokenRight)
    (same : isSameComponent (stepCupArc state position).links
      (arcEndTokenNode (stepCupArc state position) tokenLeft)
      (arcEndTokenNode (stepCupArc state position) tokenRight) = true) :
    (arcEndTokenNode (stepCupArc state position) tokenLeft < state.nextFresh
        ∧ arcEndTokenNode (stepCupArc state position) tokenRight < state.nextFresh)
      ∨ ((tokenLeft = ArcEndToken.openSlot position
            ∨ tokenLeft = ArcEndToken.openSlot (position + 1))
        ∧ (tokenRight = ArcEndToken.openSlot position
            ∨ tokenRight = ArcEndToken.openSlot (position + 1))) := by
  have legNodeAtLeast : ∀ tok : ArcEndToken,
      (tok = ArcEndToken.openSlot position ∨ tok = ArcEndToken.openSlot (position + 1)) →
      state.nextFresh ≤ arcEndTokenNode (stepCupArc state position) tok := by
    intro tok tokLeg
    cases tokLeg with
    | inl isLeft =>
        rw [isLeft]
        exact Nat.le_of_eq (arcCupLeftLegNode state position cupInRange).symm
    | inr isRight =>
        rw [isRight, arcCupRightLegNode state position cupInRange]
        exact Nat.le_succ state.nextFresh
  rcases arcCupTokenNodeClass seedBoundary state position fresh seedBelowFresh cupInRange
      tokenLeft validLeft with leftOld | leftLeg
  · rcases arcCupTokenNodeClass seedBoundary state position fresh seedBelowFresh cupInRange
        tokenRight validRight with rightOld | rightLeg
    · exact Or.inl ⟨leftOld, rightOld⟩
    · have separated := isSameComponent_stepCupArc_oldFreshProbes state position fresh forest
        (arcEndTokenNode (stepCupArc state position) tokenLeft)
        (arcEndTokenNode (stepCupArc state position) tokenRight) leftOld
        (legNodeAtLeast tokenRight rightLeg)
      exact Bool.noConfusion (separated.symm.trans same)
  · rcases arcCupTokenNodeClass seedBoundary state position fresh seedBelowFresh cupInRange
        tokenRight validRight with rightOld | rightLeg
    · have separated := isSameComponent_stepCupArc_freshOldProbes state position fresh forest
        (arcEndTokenNode (stepCupArc state position) tokenLeft)
        (arcEndTokenNode (stepCupArc state position) tokenRight)
        (legNodeAtLeast tokenLeft leftLeg) rightOld
      exact Bool.noConfusion (separated.symm.trans same)
    · exact Or.inr ⟨leftLeg, rightLeg⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-step node classification + same-component dichotomy (cup rung
D2a-iii, part 2).**  `arcCupTokenNodeClass` (every valid spliced token is old-zone or a leg),
`arcCupLeftLegNode`/`arcCupRightLegNode` (the leg node values `nextFresh`/`nextFresh+1`), and
`arcCupSameComponentDichotomy` (a same-component arc is both old-zone or both legs).  What this
marker does NOT claim: the old-zone monotone position-remap and the stepCupArc preservation of
`ArcNonCrossing` itself (the main assembly).  `= true`. -/
def fxMode_hasArcCupTokenNodeClass : Bool := true

end FX1Poly.Polygraph
