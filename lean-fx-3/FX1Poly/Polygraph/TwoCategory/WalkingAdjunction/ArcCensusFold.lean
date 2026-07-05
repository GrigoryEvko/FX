import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold

/-! # ArcCensusFold — the boundary census threads the whole chained arc fold (peel campaign H, cup rung 2d-iv)

The cap and cup preservation bricks carry the two-endpoint boundary census over ONE step; this
brick threads it through a whole boundary-chained walking-adjunction spine.  Each atom is a cup
or a cap (`adjunctionSpineAtom_hasCupOrCapArity`), its window is in range because the open-wire
count tracks the boundary 1-cell (`stepArcAtom_openWires_tracksBoundary`), and the freshness /
forestness / seed-bound companions thread exactly as in the discipline fold.  At the canonical
seed every component of the folded state touches at most two boundary endpoints — the fact the
cup rewiring's partner-scan values (rung 2d-v) pin against.

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

/-! ## The per-atom census step -/

/-- One boundary-tracked adjunction atom preserves the census: a cup via the splice
preservation (its position is in range because the generator consumes nothing), a cap via the
window preservation (its two-wire window fits inside the tracked boundary). -/
theorem arcBoundaryCensus_stepArcAtom
    {overallSource overallTarget : adjunctionGraph.Mode}
    (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (oldCensus : ArcBoundaryCensus seedBoundary state) :
    ArcBoundaryCensus seedBoundary (stepArcAtom state atom) := by
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
      exact arcBoundaryCensus_stepCupArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldCensus
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcBoundaryCensus_stepCapArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh capInRange oldCensus

/-! ## The whole-fold census transport and the canonical-seed capstone -/

/-- ★ **A chained adjunction spine's arc fold preserves the boundary census end-to-end** —
the freshness / forestness / boundary-tracking / seed-bound companions thread through the fold
exactly as in the discipline fold, and each atom's step preserves the census by the per-atom
dispatch. -/
theorem arcBoundaryCensus_processArcSpine_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcBoundaryCensus seedBoundary state →
    ArcBoundaryCensus seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, census => census
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, census => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show ArcBoundaryCensus seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact arcBoundaryCensus_processArcSpine_ofChained restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (arcBoundaryCensus_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census)

/-- ★ **The capstone at the canonical seed**: every boundary-chained walking-adjunction spine
folds from the fresh initial state to a state whose every component touches at most two
boundary endpoints (bottom ports and surviving open slots). -/
theorem arcBoundaryCensus_ofChainedSpineList
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcBoundaryCensus bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  arcBoundaryCensus_processArcSpine_ofChained atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLength bottomCount)
    chained (Nat.le_refl bottomCount) (arcBoundaryCensus_initial bottomCount)

/-- **Honesty marker — the census FOLD TRANSPORT is SHIPPED (peel campaign H, cup rung
2d-iv).**  The per-atom census step (`arcBoundaryCensus_stepArcAtom` — cup and cap windows in
range by boundary tracking), the whole-fold transport
(`arcBoundaryCensus_processArcSpine_ofChained`), and the canonical-seed capstone
(`arcBoundaryCensus_ofChainedSpineList`).  What this marker does NOT claim: the rewired
partner-scan values that CONSUME this census (rung 2d-v) and the cup-cancellation endgame.
`= true`. -/
def fxMode_hasArcCensusFoldTransport : Bool := true

end FX1Poly.Polygraph
