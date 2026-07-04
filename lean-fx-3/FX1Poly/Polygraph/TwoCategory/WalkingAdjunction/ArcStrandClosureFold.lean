import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStrandClosure
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcStrandClosureFold — a closed strand stays closed through the whole arc fold

The strand-closure fold (peel campaign H, strand-closure rung 2).  A cup step splices two
fresh legs into the open boundary and a cap step removes two reads — in both cases the new
open wires are either OLD open wires (which a closed anchor already misses) or FRESH nodes
(which it misses by the frontier field), and the queries themselves are stable by the
rung-1 per-step computations.  So `ArcStrandClosure` is preserved step by step, and
threading it through `processArcSpine` exactly as the discipline/loop folds do yields the
two payoffs: the invariant holds at the END state, and every query against the anchor at
the end state answers as at the START state.  The cap-head seed instantiation (rung 3)
consumes both to evaluate the cap head's own event indicator to zero.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Per-step invariant preservation -/

/-- **A cup step preserves the closed-strand invariant**: the spliced boundary reads either
an old open wire (below / past the splice window, missed by the open-wires field) or one of
the two fresh legs (inside the window, missed by the frontier field), and every query
against the anchor is stable by the rung-1 computation. -/
theorem arcStrandClosure_stepCupArc (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (positionInRange : position ≤ state.openWires.length)
    (closure : ArcStrandClosure anchorNode state) :
    ArcStrandClosure anchorNode (stepCupArc state position) := by
  refine ⟨?_, ?_⟩
  · intro newPosition newInRange
    rw [isSameComponent_stepCupArc_queriesStable state position forest anchorNode
      closure.missesFreshNodes]
    show isSameComponent state.links anchorNode
        (natListGetAt (natListInsertAt state.openWires position
          [state.nextFresh, state.nextFresh + 1]) newPosition)
      = false
    cases Nat.lt_or_ge newPosition position with
    | inl belowPosition =>
        have belowRead : natListGetAt (natListInsertAt state.openWires position
              [state.nextFresh, state.nextFresh + 1]) newPosition
            = natListGetAt state.openWires newPosition :=
          natListGetAt_natListInsertAt_below state.openWires position
            [state.nextFresh, state.nextFresh + 1] newPosition belowPosition
            (Nat.lt_of_lt_of_le belowPosition positionInRange)
        rw [belowRead]
        exact closure.missesOpenWires newPosition
          (Nat.lt_of_lt_of_le belowPosition positionInRange)
    | inr atOrPast =>
        obtain ⟨windowOffset, windowOffsetEq⟩ := Nat.le.dest atOrPast
        cases windowOffset with
        | zero =>
            have leftLegRead : natListGetAt (natListInsertAt state.openWires position
                  [state.nextFresh, state.nextFresh + 1]) newPosition
                = state.nextFresh := by
              rw [← windowOffsetEq]
              exact natListGetAt_natListInsertAt_inside state.openWires position
                [state.nextFresh, state.nextFresh + 1] 0
                (Nat.succ_le_succ (Nat.zero_le 1)) positionInRange
            rw [leftLegRead]
            exact closure.missesFreshNodes state.nextFresh (Nat.le_refl state.nextFresh)
        | succ innerOffset =>
            cases innerOffset with
            | zero =>
                have rightLegRead : natListGetAt (natListInsertAt state.openWires position
                      [state.nextFresh, state.nextFresh + 1]) newPosition
                    = state.nextFresh + 1 := by
                  rw [← windowOffsetEq]
                  exact natListGetAt_natListInsertAt_inside state.openWires position
                    [state.nextFresh, state.nextFresh + 1] 1 (Nat.le_refl 2)
                    positionInRange
                rw [rightLegRead]
                exact closure.missesFreshNodes (state.nextFresh + 1)
                  (Nat.le_add_right state.nextFresh 1)
            | succ pastOffset =>
                have pastRead : natListGetAt (natListInsertAt state.openWires position
                      [state.nextFresh, state.nextFresh + 1]) newPosition
                    = natListGetAt state.openWires (position + pastOffset) := by
                  rw [← windowOffsetEq]
                  exact natListGetAt_natListInsertAt_pastBlock state.openWires position
                    [state.nextFresh, state.nextFresh + 1] pastOffset positionInRange
                rw [pastRead]
                have insertedLength : (natListInsertAt state.openWires position
                      [state.nextFresh, state.nextFresh + 1]).length
                    = state.openWires.length + 2 :=
                  natListInsertAt_length state.openWires position
                    [state.nextFresh, state.nextFresh + 1]
                have pastBound : position + pastOffset < state.openWires.length := by
                  rw [← windowOffsetEq] at newInRange
                  exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
                    (Nat.lt_of_lt_of_le newInRange (Nat.le_of_eq insertedLength)))
                exact closure.missesOpenWires (position + pastOffset) pastBound
  · intro freshNode freshAtLeast
    rw [isSameComponent_stepCupArc_queriesStable state position forest anchorNode
      closure.missesFreshNodes]
    exact closure.missesFreshNodes freshNode
      (Nat.le_trans (Nat.le_add_right state.nextFresh 3) freshAtLeast)

/-- **A cap step preserves the closed-strand invariant**: the two consumed reads are open
wires the anchor misses (discharging the rung-1 read premises), the shrunken boundary reads
only old open wires (below / past the removed pair), and the frontier only advances. -/
theorem arcStrandClosure_stepCapArc (state : ArcWireState) (position : Nat)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (closure : ArcStrandClosure anchorNode state) :
    ArcStrandClosure anchorNode (stepCapArc state position) := by
  have positionBelowLength : position < state.openWires.length :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self position) (Nat.lt_succ_self (position + 1)))
      windowInRange
  have succBelowLength : position + 1 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowInRange
  have missesLeftRead : isSameComponent state.links anchorNode
      (natListGetAt state.openWires position) = false :=
    closure.missesOpenWires position positionBelowLength
  have missesRightRead : isSameComponent state.links anchorNode
      (natListGetAt state.openWires (position + 1)) = false :=
    closure.missesOpenWires (position + 1) succBelowLength
  refine ⟨?_, ?_⟩
  · intro newPosition newInRange
    rw [isSameComponent_stepCapArc_queriesStable state position forest anchorNode
      missesLeftRead missesRightRead closure.missesFreshNodes]
    show isSameComponent state.links anchorNode
        (natListGetAt (natListRemoveTwoAt state.openWires position) newPosition)
      = false
    cases Nat.lt_or_ge newPosition position with
    | inl belowPosition =>
        have belowRead : natListGetAt (natListRemoveTwoAt state.openWires position)
              newPosition
            = natListGetAt state.openWires newPosition :=
          natListGetAt_natListRemoveTwoAt_below state.openWires position newPosition
            belowPosition
        rw [belowRead]
        exact closure.missesOpenWires newPosition
          (Nat.lt_trans belowPosition positionBelowLength)
    | inr atOrPast =>
        obtain ⟨pastOffset, pastOffsetEq⟩ := Nat.le.dest atOrPast
        have pastRead : natListGetAt (natListRemoveTwoAt state.openWires position)
              newPosition
            = natListGetAt state.openWires (position + pastOffset + 2) := by
          rw [← pastOffsetEq]
          exact natListGetAt_natListRemoveTwoAt_pastPair state.openWires position
            pastOffset windowInRange
        rw [pastRead]
        have removedLength : (natListRemoveTwoAt state.openWires position).length + 2
            = state.openWires.length :=
          natListRemoveTwoAt_length state.openWires position windowInRange
        have shiftedBound : position + pastOffset + 2
            < (natListRemoveTwoAt state.openWires position).length + 2 := by
          rw [← pastOffsetEq] at newInRange
          exact Nat.succ_lt_succ (Nat.succ_lt_succ newInRange)
        exact closure.missesOpenWires (position + pastOffset + 2)
          (Nat.lt_of_lt_of_le shiftedBound (Nat.le_of_eq removedLength))
  · intro freshNode freshAtLeast
    rw [isSameComponent_stepCapArc_queriesStable state position forest anchorNode
      missesLeftRead missesRightRead closure.missesFreshNodes]
    exact closure.missesFreshNodes freshNode
      (Nat.le_trans (Nat.le_add_right state.nextFresh 1) freshAtLeast)

/-! ## Per-atom dispatch at the walking adjunction -/

/-- **One boundary-tracked adjunction atom changes no query against a closed anchor**: the
tracking premise bounds the fire window inside the boundary, the seed's arity disjunction
picks the branch, and the invariant discharges each branch's avoidance premises. -/
theorem isSameComponent_stepArcAtom_queriesStable
    {overallSource overallTarget : adjunctionGraph.Mode}
    (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (closure : ArcStrandClosure anchorNode state) (probeNode : Nat) :
    isSameComponent (stepArcAtom state atom).links anchorNode probeNode
      = isSameComponent state.links anchorNode probeNode := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjunctionSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
      exact isSameComponent_stepCupArc_queriesStable state atom.leftContext.length forest
        anchorNode closure.missesFreshNodes probeNode
  | inr capArity =>
      have windowInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, capArity.1]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      have positionBelowLength : atom.leftContext.length < state.openWires.length :=
        Nat.lt_of_lt_of_le
          (Nat.lt_trans (Nat.lt_succ_self atom.leftContext.length)
            (Nat.lt_succ_self (atom.leftContext.length + 1)))
          windowInRange
      have succBelowLength : atom.leftContext.length + 1 < state.openWires.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1)) windowInRange
      rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
      exact isSameComponent_stepCapArc_queriesStable state atom.leftContext.length forest
        anchorNode
        (closure.missesOpenWires atom.leftContext.length positionBelowLength)
        (closure.missesOpenWires (atom.leftContext.length + 1) succBelowLength)
        closure.missesFreshNodes probeNode

/-- **One boundary-tracked adjunction atom preserves the closed-strand invariant.** -/
theorem arcStrandClosure_stepArcAtom
    {overallSource overallTarget : adjunctionGraph.Mode}
    (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (forest : isUnionFindForest state.links) (anchorNode : Nat)
    (closure : ArcStrandClosure anchorNode state) :
    ArcStrandClosure anchorNode (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjunctionSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      have positionInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape]
        exact Nat.le_trans
          (Nat.le_add_right atom.leftContext.length atom.generatorDom.length)
          (Nat.le_add_right (atom.leftContext.length + atom.generatorDom.length)
            atom.rightContext.length)
      rw [stepArcAtom_eq_stepCupArc state atom cupArity.1 cupArity.2]
      exact arcStrandClosure_stepCupArc state atom.leftContext.length forest anchorNode
        positionInRange closure
  | inr capArity =>
      have windowInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, capArity.1]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom capArity.1 capArity.2]
      exact arcStrandClosure_stepCapArc state atom.leftContext.length forest anchorNode
        windowInRange closure

/-! ## The whole-spine folds -/

/-- ★ **A chained adjunction spine's arc fold preserves the closed-strand invariant
end-to-end** — the forest/tracking companions thread through the fold exactly as in the
discipline and loop folds, and each atom's step preserves the invariant. -/
theorem arcStrandClosure_processArcSpine
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength : Nat) →
    isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    (anchorNode : Nat) → ArcStrandClosure anchorNode state →
    ArcStrandClosure anchorNode (processArcSpine state atoms)
  | [], _, _, _, _, _, _, closure => closure
  | headAtom :: restAtoms, state, _, forest, tracks, chained, anchorNode, closure => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show ArcStrandClosure anchorNode
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact arcStrandClosure_processArcSpine restAtoms (stepArcAtom state headAtom)
        headAtom.codBoundaryLength
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained anchorNode
        (arcStrandClosure_stepArcAtom state headAtom tracksEntry forest anchorNode
          closure)

/-- ★ **A chained adjunction spine's arc fold changes no query against a closed anchor** —
every query at the END state answers as at the START state, by chaining the per-atom
stability through the fold (the invariant rides along to discharge each step's premises). -/
theorem isSameComponent_processArcSpine_queriesStable
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength : Nat) →
    isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    (anchorNode : Nat) → ArcStrandClosure anchorNode state →
    (probeNode : Nat) →
    isSameComponent (processArcSpine state atoms).links anchorNode probeNode
      = isSameComponent state.links anchorNode probeNode
  | [], _, _, _, _, _, _, _, _ => rfl
  | headAtom :: restAtoms, state, _, forest, tracks, chained, anchorNode, closure,
      probeNode => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show isSameComponent
          (processArcSpine (stepArcAtom state headAtom) restAtoms).links anchorNode
          probeNode
        = isSameComponent state.links anchorNode probeNode
      exact (isSameComponent_processArcSpine_queriesStable restAtoms
          (stepArcAtom state headAtom) headAtom.codBoundaryLength
          (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
          (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
          tailChained anchorNode
          (arcStrandClosure_stepArcAtom state headAtom tracksEntry forest anchorNode
            closure)
          probeNode).trans
        (isSameComponent_stepArcAtom_queriesStable state headAtom tracksEntry forest
          anchorNode closure probeNode)

/-! ## Honesty marker -/

/-- **Honesty marker — the closed-strand fold (peel campaign H, strand-closure rung 2).**
The per-step invariant preservations (cup: three-zone splice analysis, old reads missed by
the open-wires field, fresh legs by the frontier field; cap: two-zone removal analysis with
the read premises discharged from the invariant at the tracked window), the per-atom
dispatch at the walking adjunction, and the two whole-spine folds — the invariant holds at
the fold's end state, and every query against a closed anchor answers end-to-start.  What
this marker does NOT claim: the cap-head seed instantiation (the concrete
`ArcStrandClosure` witness at the peel's seed pair) and the resulting ZERO evaluation of
the cap head's event indicator in the count decomposition — the next rung.  `= true`. -/
def fxMode_hasArcStrandClosureFold : Bool := true

end FX1Poly.Polygraph
