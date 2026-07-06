import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingCapPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold

/-! # ArcPerfectMatchingFold — the token-frame perfect matching threads the whole chained arc fold (noFixedPoint rung)

The cup and cap preservation bricks carry `ArcPerfectMatchingTokens` over ONE step; this brick threads it
through a whole boundary-chained walking-adjunction spine, mirroring the census fold.  Each atom is a cup or
a cap (`adjunctionSpineAtom_hasCupOrCapArity`), its window is in range because the open-wire count tracks the
boundary 1-cell, and the freshness / forestness / seed-bound companions thread exactly as in the census fold.
The census is threaded ALONGSIDE (the cap step consumes it) via the shipped census step.

At the canonical seed every component of the folded state has exactly two boundary endpoints — the
`noFixedPoint` fact the short-chord planar lemma consumes.

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

/-! ## The per-atom perfect-matching step -/

/-- One boundary-tracked adjunction atom preserves the token-frame perfect matching: a cup via the splice
preservation, a cap via the census-coupled merge preservation (its window fits inside the tracked boundary). -/
theorem arcPerfectMatchingTokens_stepArcAtom
    {overallSource overallTarget : adjunctionGraph.Mode}
    (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (census : ArcBoundaryCensus seedBoundary state)
    (oldPerfect : ArcPerfectMatchingTokens seedBoundary state) :
    ArcPerfectMatchingTokens seedBoundary (stepArcAtom state atom) := by
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
      exact arcPerfectMatchingTokens_stepCupArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldPerfect
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcPerfectMatchingTokens_stepCapArc seedBoundary state atom.leftContext.length
        forest capInRange census oldPerfect

/-! ## The whole-fold transport and the canonical-seed capstone -/

/-- ★ **A chained adjunction spine's arc fold preserves the token-frame perfect matching end-to-end** — the
freshness / forestness / boundary-tracking / seed-bound / census companions thread through the fold exactly
as in the census fold, and each atom's step preserves the perfect matching by the per-atom dispatch. -/
theorem arcPerfectMatchingTokens_processArcSpine_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcBoundaryCensus seedBoundary state →
    ArcPerfectMatchingTokens seedBoundary state →
    ArcPerfectMatchingTokens seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, _, perfect => perfect
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, census, perfect => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show ArcPerfectMatchingTokens seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact arcPerfectMatchingTokens_processArcSpine_ofChained restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (arcBoundaryCensus_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census)
        (arcPerfectMatchingTokens_stepArcAtom seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census perfect)

/-- ★ **The capstone at the canonical seed**: every boundary-chained walking-adjunction spine folds from the
fresh initial state to a state whose every boundary token has a distinct same-component boundary token —
i.e. no fixed point, the short-chord planar lemma's third hypothesis. -/
theorem arcPerfectMatchingTokens_ofChainedSpineList
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcPerfectMatchingTokens bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  arcPerfectMatchingTokens_processArcSpine_ofChained atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLength bottomCount)
    chained (Nat.le_refl bottomCount) (arcBoundaryCensus_initial bottomCount)
    (arcPerfectMatchingTokens_initial bottomCount)

/-- **Honesty marker — the perfect-matching FOLD TRANSPORT is SHIPPED (noFixedPoint rung).**  The per-atom
step (`arcPerfectMatchingTokens_stepArcAtom` — cup/cap windows in range by boundary tracking), the whole-fold
transport (`arcPerfectMatchingTokens_processArcSpine_ofChained`, threading the census alongside for the cap
step), and the canonical-seed capstone (`arcPerfectMatchingTokens_ofChainedSpineList` — every boundary token
of the folded state has a distinct same-component partner).  What this marker does NOT claim: the
extracted-state token→range bridge that turns this into `partnerIndexOf … ≠ …` for the short-chord lemma.
`= true`. -/
def fxMode_hasArcPerfectMatchingFold : Bool := true

end FX1Poly.Polygraph
