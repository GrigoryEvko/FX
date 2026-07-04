import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # ArcComponentPersistence — component membership is monotone through the arc fold

The arc fold only JOINS components (a cup joins its fresh legs and event, a cap joins its two
read wires and event) — it never splits one.  So any same-component fact at a state persists
to every later state of the run.  This is the substrate every extract-correspondence leg
stands on: the peeled head's seed joins (the cup's event-to-leg and leg pair, the cap's
event-to-wire and consumed pair) survive to the FOLDED end state, which lets head-event
component queries reduce to queries at reindexed fresh nodes via the transfer helper.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## The query-transfer helper -/

/-- Component queries transfer along a link: when `anchorNode` and `linkedNode` share a
component, every probe answers the same against either of them. -/
theorem isSameComponent_congrOfLinked (links : List (Nat × Nat))
    (anchorNode linkedNode probeNode : Nat)
    (linked : isSameComponent links anchorNode linkedNode = true) :
    isSameComponent links anchorNode probeNode
      = isSameComponent links linkedNode probeNode := by
  cases linkedProbe : isSameComponent links linkedNode probeNode with
  | true => exact isSameComponent_trans links anchorNode linkedNode probeNode linked linkedProbe
  | false =>
      cases anchorProbe : isSameComponent links anchorNode probeNode with
      | true =>
          exact Bool.noConfusion (linkedProbe.symm.trans
            (isSameComponent_trans links linkedNode anchorNode probeNode
              (isSameComponent_flip links anchorNode linkedNode linked) anchorProbe))
      | false => rfl

/-! ## Per-step persistence -/

/-- A cup step only joins — base same-component facts persist. -/
theorem isSameComponent_stepCupArc_ofBase (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) (probeOne probeTwo : Nat)
    (base : isSameComponent state.links probeOne probeTwo = true) :
    isSameComponent (stepCupArc state position).links probeOne probeTwo = true := by
  show isSameComponent
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh) probeOne probeTwo = true
  exact isSameComponent_unionFindJoin_ofBase
    (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
    (isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest)
    (state.nextFresh + 2) state.nextFresh probeOne probeTwo
    (isSameComponent_unionFindJoin_ofBase state.links forest state.nextFresh
      (state.nextFresh + 1) probeOne probeTwo base)

/-- A cap step only joins — base same-component facts persist. -/
theorem isSameComponent_stepCapArc_ofBase (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) (probeOne probeTwo : Nat)
    (base : isSameComponent state.links probeOne probeTwo = true) :
    isSameComponent (stepCapArc state position).links probeOne probeTwo = true := by
  show isSameComponent
      (unionFindJoin
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        state.nextFresh (natListGetAt state.openWires position)) probeOne probeTwo = true
  exact isSameComponent_unionFindJoin_ofBase
    (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)))
    (isUnionFindForest_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) forest)
    state.nextFresh (natListGetAt state.openWires position) probeOne probeTwo
    (isSameComponent_unionFindJoin_ofBase state.links forest
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
      probeOne probeTwo base)

/-- One cup/cap-arity atom preserves base same-component facts (arity dispatch). -/
theorem isSameComponent_stepArcAtom_ofBase {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (forest : isUnionFindForest state.links) (probeOne probeTwo : Nat)
    (base : isSameComponent state.links probeOne probeTwo = true) :
    isSameComponent (stepArcAtom state atom).links probeOne probeTwo = true := by
  cases arity with
  | inl cupArity =>
      rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
      exact isSameComponent_stepCupArc_ofBase state atom.leftContext.length forest
        probeOne probeTwo base
  | inr capArity =>
      rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
      exact isSameComponent_stepCapArc_ofBase state atom.leftContext.length forest
        probeOne probeTwo base

/-! ## Whole-spine persistence -/

/-- ★ **Component membership is monotone through the arc fold**: any same-component fact at
the start state survives running an entire walking-adjunction spine — every step only joins,
threading the forest invariant. -/
theorem isSameComponent_processArcSpine_ofBase
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) →
    (forest : isUnionFindForest state.links) →
    (probeOne probeTwo : Nat) →
    isSameComponent state.links probeOne probeTwo = true →
    isSameComponent (processArcSpine state atoms).links probeOne probeTwo = true
  | [], _, _, _, _, base => base
  | headAtom :: restAtoms, state, forest, probeOne, probeTwo, base => by
      show isSameComponent
        (processArcSpine (stepArcAtom state headAtom) restAtoms).links probeOne probeTwo
          = true
      exact isSameComponent_processArcSpine_ofBase restAtoms (stepArcAtom state headAtom)
        (isUnionFindForest_stepArcAtom state headAtom forest) probeOne probeTwo
        (isSameComponent_stepArcAtom_ofBase state headAtom
          (adjunctionSpineAtom_hasCupOrCapArity headAtom) forest probeOne probeTwo base)

/-! ## The persistent head-seed joins at the folded end states -/

/-- Under a cup head, the head's event node stays linked to its left leg at the end state. -/
theorem arcCupHeadFolded_eventLegLinked
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (bottomCount + 2) bottomCount = true :=
  isSameComponent_processArcSpine_ofBase atoms
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (isUnionFindForest_unionFindJoin
      (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil))
    (bottomCount + 2) bottomCount
    (isSameComponent_unionFindJoin_joined
      (unionFindJoin [] bottomCount (bottomCount + 1))
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil)
      (bottomCount + 2) bottomCount)

/-- Under a cup head, the two legs stay linked at the end state. -/
theorem arcCupHeadFolded_legsLinked
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount (bottomCount + 1) = true :=
  isSameComponent_processArcSpine_ofBase atoms
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (isUnionFindForest_unionFindJoin
      (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil))
    bottomCount (bottomCount + 1)
    (isSameComponent_unionFindJoin_ofBase
      (unionFindJoin [] bottomCount (bottomCount + 1))
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil)
      (bottomCount + 2) bottomCount bottomCount (bottomCount + 1)
      (isSameComponent_unionFindJoin_joined [] isUnionFindForest_nil bottomCount
        (bottomCount + 1)))

/-- Under a cap head, the head's event node stays linked to the consumed left wire at the
end state (stated at the pinned read: the seed's wire at the window IS `windowPosition`). -/
theorem arcCapHeadFolded_eventWireLinked
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount windowPosition = true := by
  have leftWireRead : natListGetAt (List.range bottomCount) windowPosition = windowPosition :=
    rangeGetAt_below bottomCount windowPosition
      (Nat.lt_of_lt_of_le
        (Nat.lt_trans (Nat.lt_succ_self windowPosition)
          (Nat.lt_succ_self (windowPosition + 1)))
        windowFits)
  have persisted : isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      bottomCount (natListGetAt (List.range bottomCount) windowPosition) = true :=
    isSameComponent_processArcSpine_ofBase atoms
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition)
      (isUnionFindForest_unionFindJoin
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        bottomCount (natListGetAt (List.range bottomCount) windowPosition)
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil))
      bottomCount (natListGetAt (List.range bottomCount) windowPosition)
      (isSameComponent_unionFindJoin_joined
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil)
        bottomCount (natListGetAt (List.range bottomCount) windowPosition))
  rw [leftWireRead] at persisted
  exact persisted

/-- Under a cap head, the two consumed wires stay linked at the end state (stated at the
pinned reads: the seed's wires at the window ARE `windowPosition`/`windowPosition + 1`). -/
theorem arcCapHeadFolded_consumedPairLinked
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      windowPosition (windowPosition + 1) = true := by
  have leftWireRead : natListGetAt (List.range bottomCount) windowPosition = windowPosition :=
    rangeGetAt_below bottomCount windowPosition
      (Nat.lt_of_lt_of_le
        (Nat.lt_trans (Nat.lt_succ_self windowPosition)
          (Nat.lt_succ_self (windowPosition + 1)))
        windowFits)
  have rightWireRead : natListGetAt (List.range bottomCount) (windowPosition + 1)
      = windowPosition + 1 :=
    rangeGetAt_below bottomCount (windowPosition + 1) windowFits
  have persisted : isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt (List.range bottomCount) windowPosition)
      (natListGetAt (List.range bottomCount) (windowPosition + 1)) = true :=
    isSameComponent_processArcSpine_ofBase atoms
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition)
      (isUnionFindForest_unionFindJoin
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        bottomCount (natListGetAt (List.range bottomCount) windowPosition)
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil))
      (natListGetAt (List.range bottomCount) windowPosition)
      (natListGetAt (List.range bottomCount) (windowPosition + 1))
      (isSameComponent_unionFindJoin_ofBase
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        (isUnionFindForest_unionFindJoin []
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))
          isUnionFindForest_nil)
        bottomCount (natListGetAt (List.range bottomCount) windowPosition)
        (natListGetAt (List.range bottomCount) windowPosition)
        (natListGetAt (List.range bottomCount) (windowPosition + 1))
        (isSameComponent_unionFindJoin_joined [] isUnionFindForest_nil
          (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1))))
  rw [leftWireRead, rightWireRead] at persisted
  exact persisted

/-! ## Honesty marker -/

/-- **Honesty marker — component membership is MONOTONE through the arc fold, with the head
seed joins persisting to the folded end states (peel campaign H, extract-correspondence
substrate).**  Per-step and whole-spine persistence of same-component facts (the fold only
joins), the query-transfer helper along a link, and the four persistent head-seed joins: the
cup's event-to-leg and leg pair, the cap's event-to-wire and consumed pair, all at the folded
end states.  What this marker does NOT claim: the per-port internal-count and diagram legs of
the extract correspondence, the strand-closure invariant (consumed wires never re-join — a
SEPARATE fact, not monotonicity), the non-crossing invariant, and the head-cancellation
assembly.  `= true`. -/
def fxMode_hasArcComponentPersistence : Bool := true

end FX1Poly.Polygraph
