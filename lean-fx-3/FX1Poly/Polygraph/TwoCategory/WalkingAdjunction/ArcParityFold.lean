import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupParityPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapParityPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold

/-! # ArcParityFold — the opposite-class invariant threads the whole chained arc fold (peel campaign H, parity rung P-4)

The cup and cap preservation bricks carry the opposite-class strand-endpoint invariant
over ONE step; this brick threads it through a whole boundary-chained walking-adjunction
spine.  Each atom is a cup or a cap, its window is in range because the open-wire count
tracks the boundary 1-cell, and the freshness / forestness / seed-bound companions thread
exactly as in the census fold.  Both step preservations are window-parity-free, so the
fold carries a FREE source-mode parameter — the invariant holds for both global parity
assignments at once.  At the canonical seed: every strand of the folded state has its two
boundary end tokens at opposite parity classes — the fact the cup partner cancel (rung
P-5) pins the leg attachments against.

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

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The per-atom parity step -/

/-- One boundary-tracked adjunction atom preserves the opposite-class invariant: a cup via
the splice preservation (its position is in range because the generator consumes nothing),
a cap via the window preservation (its two-wire window fits inside the tracked
boundary). -/
theorem arcEndTokenParity_stepArcAtom
    {overallSource overallTarget : adjunctionGraph.Mode}
    (sourceMode : AdjunctionMode) (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (oldParity : ArcEndTokenParity sourceMode seedBoundary state) :
    ArcEndTokenParity sourceMode seedBoundary (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjunctionSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
      have cupInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape, hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right atom.leftContext.length atom.rightContext.length
      rw [stepArcAtom_eq_stepCupArc state atom hasCupDomArity hasCupCodArity]
      exact arcEndTokenParity_stepCupArc sourceMode seedBoundary state
        atom.leftContext.length fresh forest seedBelowFresh cupInRange oldParity
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcEndTokenParity_stepCapArc sourceMode seedBoundary state
        atom.leftContext.length fresh forest seedBelowFresh capInRange oldParity

/-! ## The whole-fold parity transport and the canonical-seed capstone -/

/-- ★ **A chained adjunction spine's arc fold preserves the opposite-class invariant
end-to-end** — the freshness / forestness / boundary-tracking / seed-bound companions
thread through the fold exactly as in the census fold, and each atom's step preserves the
invariant by the per-atom dispatch. -/
theorem arcEndTokenParity_processArcSpine_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode} (sourceMode : AdjunctionMode) :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcEndTokenParity sourceMode seedBoundary state →
    ArcEndTokenParity sourceMode seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, parityHolds => parityHolds
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, parityHolds => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show ArcEndTokenParity sourceMode seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact arcEndTokenParity_processArcSpine_ofChained sourceMode restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (arcEndTokenParity_stepArcAtom sourceMode seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry parityHolds)

/-- ★ **The capstone at the canonical seed**: every boundary-chained walking-adjunction
spine folds from the fresh initial state to a state whose every strand carries its two
boundary end tokens at OPPOSITE parity classes — for every source-mode assignment at
once. -/
theorem arcEndTokenParity_ofChainedSpineList
    {overallSource overallTarget : adjunctionGraph.Mode}
    (sourceMode : AdjunctionMode) (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcEndTokenParity sourceMode bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  arcEndTokenParity_processArcSpine_ofChained sourceMode atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount
    bottomCount (arcStateFresh_initial bottomCount) isUnionFindForest_nil
    (rangeLength bottomCount) chained (Nat.le_refl bottomCount)
    (arcEndTokenParity_initial sourceMode bottomCount)

/-! ## Honesty marker -/

/-- **Honesty marker — the parity FOLD TRANSPORT is SHIPPED (peel campaign H, parity rung
P-4).**  The per-atom parity step (`arcEndTokenParity_stepArcAtom` — cup and cap windows
in range by boundary tracking), the whole-fold transport
(`arcEndTokenParity_processArcSpine_ofChained`), and the canonical-seed capstone
(`arcEndTokenParity_ofChainedSpineList`) — all with a FREE source-mode parameter, since
both step preservations are window-parity-free.  What this marker does NOT claim: the cup
partner-matching cancel that CONSUMES this invariant (rung P-5) and the orbit-realignment
endgame above it.  `= true`. -/
def fxMode_hasArcParityFold : Bool := true

end FX1Poly.Polygraph
