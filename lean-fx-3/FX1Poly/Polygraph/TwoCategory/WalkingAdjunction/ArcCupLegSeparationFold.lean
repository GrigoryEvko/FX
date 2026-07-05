import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadLoops
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftStep
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSeedCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshComponentInvisibility
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCupLegSeparationFold — the cup's legs stay fresh-separated along every chained tail

The leg-separation payoff of the loop-freedom campaign (peel campaign H): on the chained
walking-adjunction fragment at `base` window parity, the FRESH tail run NEVER connects the
cup's two inserted legs — so the `legsSeparate` hypothesis of the cup-head partner dispatch
and its `FullArcStructure` capstone is DERIVABLE, and the legs-connected ("cup-cancel")
world is empty on the fragment the reconstruction runs on.

The engine is a paired-fold invariant: alongside the positional shift simulation, the
component-leg correspondence, both freshness/forest invariants, and the composite run's
typed-ends discipline, the fold threads `legs not same-component in the fresh links`.  A
cup step preserves it by fresh-join transparency at old probes; a cap step preserves it
because a connecting cap would make its two consumed wires same-component in the COMPOSITE
(through the correspondence and the seed's leg-join), where the discipline pins the window
parity to `base` against the cap's `tip` pin — the same refutation that keeps the
composite loop counter at zero.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

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

/-- Extract all three components of a failed three-way disjunction. -/
private theorem orThreeComponentsOfFalse (first second third : Bool)
    (allFail : (first || second || third) = false) :
    first = false ∧ second = false ∧ third = false := by
  cases first with
  | true => exact Bool.noConfusion allFail
  | false =>
      cases second with
      | true => exact Bool.noConfusion allFail
      | false =>
          cases third with
          | true => exact Bool.noConfusion allFail
          | false => exact ⟨rfl, rfl, rfl⟩

/-- A conjunction fails when its swap fails. -/
private theorem andFalseOfSwap (left right : Bool) (swapFails : (right && left) = false) :
    (left && right) = false := by
  cases left with
  | false => rfl
  | true =>
      cases right with
      | false => rfl
      | true => exact Bool.noConfusion swapFails

/-! ## The paired-fold invariant -/

/-- ★ **The legs stay fresh-separated along every chained fold.**  Threading the positional
shift simulation, the component-leg correspondence, both freshness/forest invariants, and
the shifted run's typed-ends discipline, the base run never connects `legLeft` to
`legLeft + 1`: a cup step is component-transparent at old probes, and a connecting cap
would make its consumed pair same-component in the SHIFTED run (through the correspondence
and the leg-join), where the discipline refutes the cap's `tip`-parity window. -/
theorem arcLegsStaySeparate_processArcSpine
    {overallSource overallTarget : adjunctionGraph.Mode}
    (sigma : Nat → Nat) (delta threshold : Nat)
    (headCupEvents headCapEvents : List Nat) (legLeft : Nat)
    (sigmaShiftsAboveThreshold : ∀ identifier, threshold ≤ identifier →
      sigma identifier = identifier + delta)
    (legRightBelowThreshold : legLeft + 1 < threshold) :
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (baseState shiftedState : ArcWireState) → (boundaryLength : Nat) →
    baseState.openWires.length = boundaryLength →
    shiftedState.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    ArcPositionalShiftSim sigma delta threshold headCupEvents headCapEvents
      baseState shiftedState →
    ArcStateFresh baseState → isUnionFindForest baseState.links →
    ArcStateFresh shiftedState → isUnionFindForest shiftedState.links →
    ArcComponentShiftCorr sigma legLeft (legLeft + 1)
      baseState.links shiftedState.links →
    ArcOpenEndsDiscipline overallSource shiftedState →
    isSameComponent baseState.links legLeft (legLeft + 1) = false →
    isSameComponent (processArcSpine baseState atoms).links legLeft (legLeft + 1) = false
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, legsSeparate => legsSeparate
  | headAtom :: restAtoms, baseState, shiftedState, _, baseTracks, shiftedTracks,
      chained, posSim, baseFresh, baseForest, shiftedFresh, shiftedForest, corr,
      discipline, legsSeparate => by
    obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
    have baseTracksEntry : baseState.openWires.length = headAtom.domBoundaryLength :=
      baseTracks.trans headFires.symm
    have shiftedTracksEntry : shiftedState.openWires.length = headAtom.domBoundaryLength :=
      shiftedTracks.trans headFires.symm
    have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
    have legRightBelowNextFresh : legLeft + 1 < baseState.nextFresh :=
      Nat.lt_of_lt_of_le legRightBelowThreshold posSim.nfFloor
    have legLeftBelowNextFresh : legLeft < baseState.nextFresh :=
      Nat.lt_trans (Nat.lt_succ_self legLeft) legRightBelowNextFresh
    have steppedSeparate : isSameComponent (stepArcAtom baseState headAtom).links
        legLeft (legLeft + 1) = false := by
      cases headArity with
      | inl cupArity =>
          obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
          rw [stepArcAtom_eq_stepCupArc baseState headAtom hasCupDomArity hasCupCodArity,
            isSameComponent_stepCupArc_oldProbes baseState headAtom.leftContext.length
              baseFresh baseForest legLeft (legLeft + 1) legLeftBelowNextFresh
              legRightBelowNextFresh]
          exact legsSeparate
      | inr capArity =>
          obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
          have baseEntryShape : baseState.openWires.length
              = headAtom.leftContext.length + headAtom.generatorDom.length
                + headAtom.rightContext.length := baseTracksEntry
          have baseWindowInRange : headAtom.leftContext.length + 2
              ≤ baseState.openWires.length := by
            rw [baseEntryShape, hasCapDomArity]
            exact Nat.le_add_right (headAtom.leftContext.length + 2)
              headAtom.rightContext.length
          have windowBelowBaseLength : headAtom.leftContext.length
              < baseState.openWires.length :=
            Nat.lt_of_lt_of_le
              (Nat.lt_trans (Nat.lt_succ_self headAtom.leftContext.length)
                (Nat.lt_succ_self (headAtom.leftContext.length + 1)))
              baseWindowInRange
          have windowSuccBelowBaseLength : headAtom.leftContext.length + 1
              < baseState.openWires.length :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self (headAtom.leftContext.length + 1))
              baseWindowInRange
          have shiftedEntryShape : shiftedState.openWires.length
              = headAtom.leftContext.length + headAtom.generatorDom.length
                + headAtom.rightContext.length := shiftedTracksEntry
          have shiftedWindowInRange : headAtom.leftContext.length + 2
              ≤ shiftedState.openWires.length := by
            rw [shiftedEntryShape, hasCapDomArity]
            exact Nat.le_add_right (headAtom.leftContext.length + 2)
              headAtom.rightContext.length
          have windowSuccBelowShiftedLength : headAtom.leftContext.length + 1
              < shiftedState.openWires.length :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self (headAtom.leftContext.length + 1))
              shiftedWindowInRange
          have shiftedConsumedSeparate : isSameComponent shiftedState.links
              (natListGetAt shiftedState.openWires headAtom.leftContext.length)
              (natListGetAt shiftedState.openWires (headAtom.leftContext.length + 1))
              = false := by
            cases sameEq : isSameComponent shiftedState.links
                (natListGetAt shiftedState.openWires headAtom.leftContext.length)
                (natListGetAt shiftedState.openWires
                  (headAtom.leftContext.length + 1)) with
            | false => rfl
            | true =>
                have pinned := discipline headAtom.leftContext.length
                  (headAtom.leftContext.length + 1)
                  (Nat.lt_succ_self headAtom.leftContext.length)
                  windowSuccBelowShiftedLength sameEq
                exact AdjunctionMode.noConfusion
                  ((adjunctionCapAtom_windowPositionMode headAtom
                    hasCapDomArity).symm.trans pinned.1)
          have leftImage : natListGetAt shiftedState.openWires
              headAtom.leftContext.length
            = sigma (natListGetAt baseState.openWires headAtom.leftContext.length) := by
            rw [posSim.openMap]
            exact natListGetAt_map_inRange sigma baseState.openWires
              headAtom.leftContext.length windowBelowBaseLength
          have rightImage : natListGetAt shiftedState.openWires
              (headAtom.leftContext.length + 1)
            = sigma
                (natListGetAt baseState.openWires (headAtom.leftContext.length + 1)) := by
            rw [posSim.openMap]
            exact natListGetAt_map_inRange sigma baseState.openWires
              (headAtom.leftContext.length + 1) windowSuccBelowBaseLength
          rw [leftImage, rightImage] at shiftedConsumedSeparate
          have joinedSeparate : isSameComponent
              (unionFindJoin baseState.links legLeft (legLeft + 1))
              (natListGetAt baseState.openWires headAtom.leftContext.length)
              (natListGetAt baseState.openWires (headAtom.leftContext.length + 1))
              = false :=
            (corr (natListGetAt baseState.openWires headAtom.leftContext.length)
              (natListGetAt baseState.openWires
                (headAtom.leftContext.length + 1))).symm.trans shiftedConsumedSeparate
          rw [isSameComponent_unionFindJoin baseState.links baseForest legLeft
            (legLeft + 1) (natListGetAt baseState.openWires headAtom.leftContext.length)
            (natListGetAt baseState.openWires (headAtom.leftContext.length + 1))]
            at joinedSeparate
          obtain ⟨_consumedSeparate, crossHeadFails, crossSwapFails⟩ :=
            orThreeComponentsOfFalse
              (isSameComponent baseState.links
                (natListGetAt baseState.openWires headAtom.leftContext.length)
                (natListGetAt baseState.openWires (headAtom.leftContext.length + 1)))
              (isSameComponent baseState.links legLeft
                  (natListGetAt baseState.openWires headAtom.leftContext.length)
                && isSameComponent baseState.links (legLeft + 1)
                  (natListGetAt baseState.openWires (headAtom.leftContext.length + 1)))
              (isSameComponent baseState.links legLeft
                  (natListGetAt baseState.openWires (headAtom.leftContext.length + 1))
                && isSameComponent baseState.links
                  (natListGetAt baseState.openWires headAtom.leftContext.length)
                  (legLeft + 1))
              joinedSeparate
          have secondFails : (isSameComponent baseState.links
                (natListGetAt baseState.openWires headAtom.leftContext.length) legLeft
              && isSameComponent baseState.links
                (natListGetAt baseState.openWires (headAtom.leftContext.length + 1))
                (legLeft + 1)) = false := by
            rw [isSameComponent_symm baseState.links
                (natListGetAt baseState.openWires headAtom.leftContext.length) legLeft,
              isSameComponent_symm baseState.links
                (natListGetAt baseState.openWires (headAtom.leftContext.length + 1))
                (legLeft + 1)]
            exact crossHeadFails
          have thirdFails : (isSameComponent baseState.links
                (natListGetAt baseState.openWires headAtom.leftContext.length)
                (legLeft + 1)
              && isSameComponent baseState.links legLeft
                (natListGetAt baseState.openWires (headAtom.leftContext.length + 1)))
              = false :=
            andFalseOfSwap
              (isSameComponent baseState.links
                (natListGetAt baseState.openWires headAtom.leftContext.length)
                (legLeft + 1))
              (isSameComponent baseState.links legLeft
                (natListGetAt baseState.openWires (headAtom.leftContext.length + 1)))
              crossSwapFails
          rw [stepArcAtom_eq_stepCapArc baseState headAtom hasCapDomArity hasCapCodArity,
            isSameComponent_stepCapArc_oldProbes baseState headAtom.leftContext.length
              baseFresh baseForest legLeft (legLeft + 1) legLeftBelowNextFresh
              legRightBelowNextFresh,
            isSameComponent_unionFindJoin baseState.links baseForest
              (natListGetAt baseState.openWires headAtom.leftContext.length)
              (natListGetAt baseState.openWires (headAtom.leftContext.length + 1))
              legLeft (legLeft + 1),
            legsSeparate, secondFails, thirdFails]
          rfl
    show isSameComponent
        (processArcSpine (stepArcAtom baseState headAtom) restAtoms).links
        legLeft (legLeft + 1) = false
    exact arcLegsStaySeparate_processArcSpine sigma delta threshold headCupEvents
      headCapEvents legLeft sigmaShiftsAboveThreshold legRightBelowThreshold restAtoms
      (stepArcAtom baseState headAtom) (stepArcAtom shiftedState headAtom)
      headAtom.codBoundaryLength
      (stepArcAtom_openWires_tracksBoundary baseState headAtom headArity baseTracksEntry)
      (stepArcAtom_openWires_tracksBoundary shiftedState headAtom headArity
        shiftedTracksEntry)
      tailChained
      (arcPositionalShiftSim_stepArcAtom sigma delta threshold headCupEvents headCapEvents
        baseState shiftedState headAtom headArity sigmaShiftsAboveThreshold posSim)
      (arcStateFresh_stepArcAtom baseState headAtom baseFresh)
      (isUnionFindForest_stepArcAtom_ofCupOrCap baseState headAtom headArity baseForest)
      (arcStateFresh_stepArcAtom shiftedState headAtom shiftedFresh)
      (isUnionFindForest_stepArcAtom_ofCupOrCap shiftedState headAtom headArity
        shiftedForest)
      (arcComponentShiftCorr_stepArcAtom sigma delta threshold headCupEvents headCapEvents
        legLeft (legLeft + 1) baseState shiftedState headAtom headArity baseTracksEntry
        sigmaShiftsAboveThreshold posSim baseForest shiftedForest corr)
      (arcOpenEndsDiscipline_stepArcAtom shiftedState headAtom shiftedFresh shiftedForest
        shiftedTracksEntry discipline)
      steppedSeparate

/-! ## The seed payoff -/

/-- ★ **The cup's legs stay fresh-separated on the chained fragment at `base` parity** —
the `legsSeparate` hypothesis of the cup-head partner dispatch, the diagram leg, and the
`FullArcStructure` capstone is DERIVABLE: the legs-connected ("cup-cancel") world is EMPTY
on the fragment the reconstruction runs on. -/
theorem arcCupHeadFolded_legsSeparate
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (windowParityIsBase :
      adjunctionModeAtDistance overallSource windowPosition = AdjunctionMode.base)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) :
    isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      windowPosition (windowPosition + 1) = false :=
  arcLegsStaySeparate_processArcSpine
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] [] windowPosition
    (arcHeadReindex_cupSeedShifts bottomCount windowPosition)
    (Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits))
    atoms
    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (bottomCount + 2)
    (rangeLength (bottomCount + 2))
    (cupHeadOpenWires_length bottomCount windowPosition)
    chained
    (arcPositionalShiftSim_cupHeadSeed bottomCount windowPosition)
    (arcStateFresh_initial (bottomCount + 2))
    isUnionFindForest_nil
    (stepCupArc_arcStateFresh
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      (arcStateFresh_initial bottomCount))
    (isUnionFindForest_stepCupArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      isUnionFindForest_nil)
    (arcComponentShiftCorr_cupHeadSeedState bottomCount windowPosition windowFits)
    (arcOpenEndsDiscipline_cupHeadSeed overallSource bottomCount windowPosition windowFits
      windowParityIsBase)
    (decide_eq_false (fun legsEqual =>
      Nat.lt_irrefl windowPosition
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
          (Nat.le_of_eq
            (show windowPosition + 1 = windowPosition from legsEqual.symm)))))

/-! ## Honesty marker -/

/-- **Honesty marker — the cup legs stay fresh-separated along every chained tail (peel
campaign H, the leg-separation payoff).**  `arcLegsStaySeparate_processArcSpine`: the
paired-fold invariant — a cup step is component-transparent at old probes, and a
connecting cap dies on the shifted run's typed-ends discipline through the component
correspondence.  `arcCupHeadFolded_legsSeparate`: at the cup-head seed (chained fragment,
`base` window parity) the fresh tail run never connects the inserted legs — the
`legsSeparate` hypothesis of `arcCupHeadFolded_partnerDispatch` /
`arcCupHeadFolded_extractDiagram` / `arcCupHeadFolded_extractArc` is derivable, and the
legs-connected ("cup-cancel") world is EMPTY on the reconstruction fragment.  What this
marker does NOT claim: the head-location driver discharging
`SpineArcHeadExtractionChained`.  `= true`. -/
def fxMode_hasArcCupLegSeparationFold : Bool := true

end FX1Poly.Polygraph
