import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingCapMain
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold

/-! # ArcNonCrossingFold — the non-crossing invariant threads the whole arc fold (cap rung D2a-iv, fold)

The cup and cap preservation bricks carry `ArcNonCrossing` over ONE step; this brick threads it
through a whole boundary-chained walking-adjunction spine.  Because the cap preservation consumes
the boundary census (its wire-join dispatch needs the two-endpoint bound), the fold threads BOTH
`ArcBoundaryCensus` AND `ArcNonCrossing` together — the census by `arcBoundaryCensus_stepArcAtom`,
the non-crossing by `arcNonCrossing_stepArcAtom` — with the same freshness / forestness /
boundary-tracking / seed-bound companions as the census fold.  At the canonical seed both hold, so
every boundary-chained spine folds to a state whose union-find matching is planar.

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

/-! ## The per-atom non-crossing step -/

/-- One boundary-tracked adjunction atom preserves the non-crossing invariant: a cup via the
splice preservation (needing only the old invariant), a cap via the join preservation (needing the
old census too — the cap fuses two components). -/
theorem arcNonCrossing_stepArcAtom
    {overallSource overallTarget : adjunctionGraph.Mode}
    (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (oldCensus : ArcBoundaryCensus seedBoundary state)
    (oldNonCrossing : ArcNonCrossing seedBoundary state) :
    ArcNonCrossing seedBoundary (stepArcAtom state atom) := by
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
      exact arcNonCrossing_stepCupArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldNonCrossing
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcNonCrossing_stepCapArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh capInRange oldCensus oldNonCrossing

/-! ## The whole-fold transport and the canonical-seed capstone -/

/-- ★ **A chained adjunction spine's arc fold preserves the non-crossing invariant end-to-end** —
threading the census (needed at each cap step) and the non-crossing invariant together, with the
freshness / forestness / boundary-tracking / seed-bound companions exactly as in the census fold. -/
theorem arcNonCrossing_processArcSpine_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcBoundaryCensus seedBoundary state →
    ArcNonCrossing seedBoundary state →
    ArcNonCrossing seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, _, nonCrossing => nonCrossing
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, census, nonCrossing => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show ArcNonCrossing seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact arcNonCrossing_processArcSpine_ofChained restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (arcBoundaryCensus_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census)
        (arcNonCrossing_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census nonCrossing)

/-- ★ **The capstone at the canonical seed**: every boundary-chained walking-adjunction spine
folds from the fresh initial state to a state whose union-find matching is planar (non-crossing). -/
theorem arcNonCrossing_ofChainedSpineList
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcNonCrossing bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  arcNonCrossing_processArcSpine_ofChained atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLength bottomCount)
    chained (Nat.le_refl bottomCount)
    (arcBoundaryCensus_initial bottomCount) (arcNonCrossing_initial bottomCount)

/-- **Honesty marker — the non-crossing FOLD TRANSPORT is SHIPPED (cap rung D2a-iv, fold).**  The
per-atom non-crossing step (`arcNonCrossing_stepArcAtom` — cup and cap windows in range by boundary
tracking), the whole-fold transport threading census-and-non-crossing
(`arcNonCrossing_processArcSpine_ofChained`), and the canonical-seed capstone
(`arcNonCrossing_ofChainedSpineList`).  What this marker does NOT claim: the extract translation to
`IsNonCrossing bottomCount (…).diagram.partner` (the last D2a-iv rung) and the leg-aligned cup
selector that consumes the planar partition (D1/D2).  `= true`. -/
def fxMode_hasArcNonCrossingFoldTransport : Bool := true

end FX1Poly.Polygraph
