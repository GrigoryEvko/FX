import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold

/-! # ArcLoopFreedom — chained adjunction folds never close a loop

The campaign-C payoff: at a DISCIPLINED state, a cap's two consumed wires cannot already
share a component — the discipline instance at the window pair `(position, position + 1)`
would type the window position `base`, against the cap's `tip` parity pin.  So the cap's
`wasSameComponent` guard is `false`, the loop counter never increments, and (threading the
discipline through the fold exactly as `ArcDisciplineFold` does) every boundary-chained
walking-adjunction spine folds from the canonical seed with `loops = 0` — down to the
extracted `DiagramType`.  This is the circle-freedom fact the peel's H campaign consumes.

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

/-! ## The per-step refutation — a disciplined cap cannot close a loop -/

/-- ★ **A cap at a disciplined state keeps the loop count.**  Were the two consumed wires
already same-component, the discipline instance at the pair `(position, position + 1)`
would pin the window position's parity to `base` — against the cap's `tip` pin.  So the
`wasSameComponent` guard is `false` and the counter stands. -/
theorem stepCapArc_loops_ofDisciplined (sourceMode : AdjunctionMode)
    (state : ArcWireState) (position : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (windowParityIsTip : adjunctionModeAtDistance sourceMode position = AdjunctionMode.tip)
    (discipline : ArcOpenEndsDiscipline sourceMode state) :
    (stepCapArc state position).loops = state.loops := by
  have windowSuccBelowLength : position + 1 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowInRange
  have consumedWiresNotSameComponent : isSameComponent state.links
      (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) = false := by
    cases sameEq : isSameComponent state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)) with
    | false => rfl
    | true =>
        have pinned := discipline position (position + 1) (Nat.lt_succ_self position)
          windowSuccBelowLength sameEq
        exact AdjunctionMode.noConfusion (windowParityIsTip.symm.trans pinned.1)
  show (if isSameComponent state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1))
        then state.loops + 1 else state.loops)
     = state.loops
  rw [consumedWiresNotSameComponent]
  exact if_neg (fun falseEqTrue => Bool.noConfusion falseEqTrue)

/-- One boundary-tracked adjunction atom keeps the loop count: a cup keeps it outright,
and a cap keeps it by the discipline refutation at its `tip`-parity window. -/
theorem stepArcAtom_loops_ofDisciplined
    {overallSource overallTarget : adjunctionGraph.Mode}
    (state : ArcWireState)
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (discipline : ArcOpenEndsDiscipline overallSource state) :
    (stepArcAtom state atom).loops = state.loops := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases adjunctionSpineAtom_hasCupOrCapArity atom with
  | inl cupArity =>
      obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
      rw [stepArcAtom_eq_stepCupArc state atom hasCupDomArity hasCupCodArity]
      rfl
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have windowInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact stepCapArc_loops_ofDisciplined overallSource state atom.leftContext.length
        windowInRange (adjunctionCapAtom_windowPositionMode atom hasCapDomArity) discipline

/-! ## The whole-fold loop constancy and the canonical-seed capstone -/

/-- ★ **A chained adjunction spine's arc fold keeps the loop count end-to-end** — the
discipline (with its freshness / forestness / tracking companions) threads through the fold
exactly as in `arcOpenEndsDiscipline_processArcSpine`, and each atom's step keeps the count
by the discipline refutation. -/
theorem processArcSpine_loops_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    ArcOpenEndsDiscipline overallSource state →
    (processArcSpine state atoms).loops = state.loops
  | [], _, _, _, _, _, _, _ => rfl
  | headAtom :: restAtoms, state, _, fresh, forest, tracks, chained, discipline => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      show (processArcSpine (stepArcAtom state headAtom) restAtoms).loops = state.loops
      have restKeepLoops := processArcSpine_loops_ofChained restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (arcOpenEndsDiscipline_stepArcAtom state headAtom fresh forest tracksEntry
          discipline)
      exact restKeepLoops.trans
        (stepArcAtom_loops_ofDisciplined state headAtom tracksEntry discipline)

/-- ★ **The capstone at the canonical seed**: every boundary-chained walking-adjunction
spine folds from the fresh initial state with `loops = 0` — no cap along the fold ever
closes a circle. -/
theorem arcFoldLoops_zero_ofChainedSpineList
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).loops = 0 :=
  processArcSpine_loops_ofChained atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLength bottomCount)
    chained (arcOpenEndsDiscipline_initial overallSource bottomCount)

/-- ★ **The extracted diagram of a chained adjunction spine is CIRCLE-FREE** — the
`DiagramType` read by `arcStructureOfSpineList` (and hence by `arcStructureOf` on any
walking-adjunction 2-cell whose spine is boundary-chained) reports `loops = 0`. -/
theorem arcStructureOfSpineList_diagramLoops_zero_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    (arcStructureOfSpineList bottomCount atoms).diagram.loops = 0 := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).loops = 0
  exact arcFoldLoops_zero_ofChainedSpineList bottomCount atoms chained

/-! ## Honesty marker -/

/-- **Honesty marker — the LOOP-FREEDOM consequence is SHIPPED (peel campaign C, rung 3).**
The disciplined-cap refutation (`stepCapArc_loops_ofDisciplined` — the same-component
premise feeds the discipline pair at the window, `base` against the `tip` pin), the
per-atom step (`stepArcAtom_loops_ofDisciplined`), the whole-fold constancy
(`processArcSpine_loops_ofChained`), the canonical-seed capstone
(`arcFoldLoops_zero_ofChainedSpineList`), and the extracted-diagram reading
(`arcStructureOfSpineList_diagramLoops_zero_ofChained`).  What this marker does NOT claim:
the leg-separation payoff and the head-cancellation reindex (campaign H), which CONSUME
this circle-freedom.  `= true`. -/
def fxMode_hasArcLoopFreedom : Bool := true

end FX1Poly.Polygraph
