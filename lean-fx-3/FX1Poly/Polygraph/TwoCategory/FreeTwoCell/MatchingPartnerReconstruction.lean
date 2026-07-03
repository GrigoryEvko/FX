import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingViewSimulation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # mode-3 — the extract→view reconstruction (the partner map DETERMINES the view)

`extractDiagram_eq_of_connectivityView` ships the forward direction: the connectivity view
determines the extract.  This file ships the CONVERSE — the extracted partner map determines
the connectivity view — closing the loop: extract equality and view agreement are
interchangeable at in-range boundary indices, with NO freshness conditions.

  * `diagramSameComponentView` — the Boolean view a diagram's partner map encodes: two
    boundary indices are same-component iff they are equal, one is the other's partner, or
    they share a partner that is a genuine find (`partner ≠ self`).  The trichotomy shape is
    exactly what `findPartnerScan_excludeAgree` produces — no first-of-component function is
    ever materialized;
  * ★ `matchingSameComponent_eq_diagramView` — the per-state characterization: at in-range
    indices the union-find same-component Boolean EQUALS the partner-map view.  Soundness
    closes the different-root direction (a found partner shares the root); completeness + the
    exclude-agreement trichotomy close the same-root direction;
  * ★ `matchingConnectivityViewSim_ofExtractEq` — the reconstruction: equal extracts yield
    the full `MatchingConnectivityViewSim` (lengths and loops by field congruence, the view by
    characterizing both sides and rewriting the extract equality).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range read plumbing (hand-rolled; core range lemmas leak `propext`) -/

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

private theorem memRangeLoop_of : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target < count ∨ target ∈ accumulated →
    target ∈ List.range.loop count accumulated
  | 0, _, _, targetSource => by
      cases targetSource with
      | inl below => exact absurd below (Nat.not_succ_le_zero _)
      | inr inAccumulated => exact inAccumulated
  | count + 1, accumulated, target, targetSource =>
      memRangeLoop_of count (count :: accumulated) target (by
        cases targetSource with
        | inr inAccumulated => exact Or.inr (List.Mem.tail count inAccumulated)
        | inl below =>
            cases Nat.lt_or_ge target count with
            | inl belowCount => exact Or.inl belowCount
            | inr atLeast =>
                have targetEq : target = count :=
                  Nat.le_antisymm (Nat.le_of_succ_le_succ below) atLeast
                rw [targetEq]
                exact Or.inr (List.Mem.head accumulated))

private theorem memRange_ofBelow (count target : Nat) (targetBelow : target < count) :
    target ∈ List.range count :=
  memRangeLoop_of count [] target (Or.inl targetBelow)

/-! ## The partner-map view -/

/-- Read a diagram's partner map at a boundary index. -/
def diagramPartnerAt (diagram : DiagramType) (index : Nat) : Nat :=
  natListGetAt diagram.partner index

/-- **The Boolean same-component view a diagram's partner map encodes**: two boundary indices
share a component iff they are equal, one is the other's partner, or they share a partner
that is a genuine find (the partner differs from its own index). -/
def diagramSameComponentView (diagram : DiagramType) (firstIndex secondIndex : Nat) : Bool :=
  firstIndex == secondIndex
    || diagramPartnerAt diagram firstIndex == secondIndex
    || diagramPartnerAt diagram secondIndex == firstIndex
    || (diagramPartnerAt diagram firstIndex == diagramPartnerAt diagram secondIndex
        && !(diagramPartnerAt diagram firstIndex == firstIndex))

/-- The extracted partner map reads back the partner function at every in-range index. -/
theorem diagramPartnerAt_extract (bottomCount : Nat) (state : WireState) (index : Nat)
    (indexInRange : index < bottomCount + state.openWires.length) :
    diagramPartnerAt (extractDiagram bottomCount state) index
      = partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
          (bottomCount + state.openWires.length) index := by
  show natListGetAt ((List.range (bottomCount + state.openWires.length)).map
        (partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
          (bottomCount + state.openWires.length))) index
    = partnerIndexOf state.links (matchingBoundaryNodes bottomCount state)
        (bottomCount + state.openWires.length) index
  have indexInMapped : index < (List.range (bottomCount + state.openWires.length)).length := by
    rw [rangeLength (bottomCount + state.openWires.length)]
    exact indexInRange
  rw [natListGetAt_map_inRange (partnerIndexOf state.links
        (matchingBoundaryNodes bottomCount state) (bottomCount + state.openWires.length))
      (List.range (bottomCount + state.openWires.length)) index indexInMapped,
    rangeGetAt_below (bottomCount + state.openWires.length) index indexInRange]

/-! ## The per-state characterization -/

/-- ★ **The union-find same-component Boolean EQUALS the partner-map view** at in-range
boundary indices — unconditionally.  Same-root direction: completeness forces both scans to
find, and the exclude-agreement trichotomy lands in one of the three non-diagonal disjuncts.
Different-root direction: scan soundness refutes each disjunct. -/
theorem matchingSameComponent_eq_diagramView (bottomCount : Nat) (state : WireState)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < bottomCount + state.openWires.length)
    (secondInRange : secondIndex < bottomCount + state.openWires.length) :
    matchingSameComponent bottomCount state firstIndex secondIndex
      = diagramSameComponentView (extractDiagram bottomCount state) firstIndex secondIndex
    := by
  show (unionFindRootOf state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
      == unionFindRootOf state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
    = (firstIndex == secondIndex
        || diagramPartnerAt (extractDiagram bottomCount state) firstIndex == secondIndex
        || diagramPartnerAt (extractDiagram bottomCount state) secondIndex == firstIndex
        || (diagramPartnerAt (extractDiagram bottomCount state) firstIndex
              == diagramPartnerAt (extractDiagram bottomCount state) secondIndex
            && !(diagramPartnerAt (extractDiagram bottomCount state) firstIndex
              == firstIndex)))
  rw [diagramPartnerAt_extract bottomCount state firstIndex firstInRange,
    diagramPartnerAt_extract bottomCount state secondIndex secondInRange]
  cases hEqIdx : (firstIndex == secondIndex) with
  | true =>
      rw [of_decide_eq_true hEqIdx]
      have selfRoot : (unionFindRootOf state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)
          == unionFindRootOf state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)) = true :=
        decide_eq_true rfl
      rw [selfRoot]
      rfl
  | false =>
      have idxNe : firstIndex ≠ secondIndex := of_decide_eq_false hEqIdx
      cases hRoots : (unionFindRootOf state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
          == unionFindRootOf state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)) with
      | true =>
          have rootsEq : unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
              = unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex) :=
            of_decide_eq_true hRoots
          have firstScanNe : findPartnerScan state.links
              (matchingBoundaryNodes bottomCount state)
              (unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
              firstIndex (List.range (bottomCount + state.openWires.length)) ≠ firstIndex :=
            findPartnerScan_neExclude_ofTarget state.links
              (matchingBoundaryNodes bottomCount state)
              (unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
              firstIndex (List.range (bottomCount + state.openWires.length)) secondIndex
              (memRange_ofBelow (bottomCount + state.openWires.length) secondIndex
                secondInRange)
              (fun secondEq => idxNe secondEq.symm) rootsEq.symm
          have secondScanNe : findPartnerScan state.links
              (matchingBoundaryNodes bottomCount state)
              (unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
              secondIndex (List.range (bottomCount + state.openWires.length))
              ≠ secondIndex :=
            findPartnerScan_neExclude_ofTarget state.links
              (matchingBoundaryNodes bottomCount state)
              (unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
              secondIndex (List.range (bottomCount + state.openWires.length)) firstIndex
              (memRange_ofBelow (bottomCount + state.openWires.length) firstIndex
                firstInRange)
              idxNe rfl
          have secondPartnerEq : partnerIndexOf state.links
              (matchingBoundaryNodes bottomCount state)
              (bottomCount + state.openWires.length) secondIndex
              = findPartnerScan state.links (matchingBoundaryNodes bottomCount state)
                (unionFindRootOf state.links
                  (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
                secondIndex (List.range (bottomCount + state.openWires.length)) := by
            show findPartnerScan state.links (matchingBoundaryNodes bottomCount state)
                (unionFindRootOf state.links
                  (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
                secondIndex (List.range (bottomCount + state.openWires.length))
              = findPartnerScan state.links (matchingBoundaryNodes bottomCount state)
                (unionFindRootOf state.links
                  (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
                secondIndex (List.range (bottomCount + state.openWires.length))
            rw [rootsEq]
          cases findPartnerScan_excludeAgree state.links
              (matchingBoundaryNodes bottomCount state)
              (unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
              firstIndex secondIndex (List.range (bottomCount + state.openWires.length))
              firstScanNe secondScanNe with
          | inl scanFirstEq =>
              have d2 : (partnerIndexOf state.links
                    (matchingBoundaryNodes bottomCount state)
                    (bottomCount + state.openWires.length) firstIndex == secondIndex)
                  = true :=
                decide_eq_true scanFirstEq
              rw [d2]
              rfl
          | inr rest =>
              cases rest with
              | inl scanSecondEq =>
                  have d3 : (partnerIndexOf state.links
                        (matchingBoundaryNodes bottomCount state)
                        (bottomCount + state.openWires.length) secondIndex == firstIndex)
                      = true :=
                    decide_eq_true (secondPartnerEq.trans scanSecondEq)
                  rw [d3]
                  cases hDTwo : (partnerIndexOf state.links
                      (matchingBoundaryNodes bottomCount state)
                      (bottomCount + state.openWires.length) firstIndex == secondIndex) with
                  | true => rfl
                  | false => rfl
              | inr scansAgree =>
                  have dFour : (partnerIndexOf state.links
                        (matchingBoundaryNodes bottomCount state)
                        (bottomCount + state.openWires.length) firstIndex
                      == partnerIndexOf state.links
                        (matchingBoundaryNodes bottomCount state)
                        (bottomCount + state.openWires.length) secondIndex) = true :=
                    decide_eq_true (scansAgree.trans secondPartnerEq.symm)
                  have dSelf : (partnerIndexOf state.links
                        (matchingBoundaryNodes bottomCount state)
                        (bottomCount + state.openWires.length) firstIndex == firstIndex)
                      = false :=
                    decide_eq_false firstScanNe
                  rw [dFour, dSelf]
                  cases hDTwo : (partnerIndexOf state.links
                      (matchingBoundaryNodes bottomCount state)
                      (bottomCount + state.openWires.length) firstIndex == secondIndex) with
                  | true => rfl
                  | false =>
                      cases hDThree : (partnerIndexOf state.links
                          (matchingBoundaryNodes bottomCount state)
                          (bottomCount + state.openWires.length) secondIndex
                          == firstIndex) with
                      | true => rfl
                      | false => rfl
      | false =>
          have rootsNe : ¬(unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
              = unionFindRootOf state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex)) :=
            of_decide_eq_false hRoots
          have dTwo : (partnerIndexOf state.links
                (matchingBoundaryNodes bottomCount state)
                (bottomCount + state.openWires.length) firstIndex == secondIndex)
              = false :=
            decide_eq_false fun partnerEq => by
              have scanEq : findPartnerScan state.links
                  (matchingBoundaryNodes bottomCount state)
                  (unionFindRootOf state.links
                    (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
                  firstIndex (List.range (bottomCount + state.openWires.length))
                  = secondIndex := partnerEq
              have scanNe : findPartnerScan state.links
                  (matchingBoundaryNodes bottomCount state)
                  (unionFindRootOf state.links
                    (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
                  firstIndex (List.range (bottomCount + state.openWires.length))
                  ≠ firstIndex := by
                rw [scanEq]
                exact fun secondEq => idxNe secondEq.symm
              have soundRoot := findPartnerScan_root_ofFound state.links
                (matchingBoundaryNodes bottomCount state)
                (unionFindRootOf state.links
                  (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
                firstIndex (List.range (bottomCount + state.openWires.length)) scanNe
              rw [scanEq] at soundRoot
              exact rootsNe soundRoot.symm
          have dThree : (partnerIndexOf state.links
                (matchingBoundaryNodes bottomCount state)
                (bottomCount + state.openWires.length) secondIndex == firstIndex)
              = false :=
            decide_eq_false fun partnerEq => by
              have scanEq : findPartnerScan state.links
                  (matchingBoundaryNodes bottomCount state)
                  (unionFindRootOf state.links
                    (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
                  secondIndex (List.range (bottomCount + state.openWires.length))
                  = firstIndex := partnerEq
              have scanNe : findPartnerScan state.links
                  (matchingBoundaryNodes bottomCount state)
                  (unionFindRootOf state.links
                    (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
                  secondIndex (List.range (bottomCount + state.openWires.length))
                  ≠ secondIndex := by
                rw [scanEq]
                exact idxNe
              have soundRoot := findPartnerScan_root_ofFound state.links
                (matchingBoundaryNodes bottomCount state)
                (unionFindRootOf state.links
                  (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
                secondIndex (List.range (bottomCount + state.openWires.length)) scanNe
              rw [scanEq] at soundRoot
              exact rootsNe soundRoot
          have dFour : ((partnerIndexOf state.links
                (matchingBoundaryNodes bottomCount state)
                (bottomCount + state.openWires.length) firstIndex
              == partnerIndexOf state.links
                (matchingBoundaryNodes bottomCount state)
                (bottomCount + state.openWires.length) secondIndex)
              && !(partnerIndexOf state.links
                (matchingBoundaryNodes bottomCount state)
                (bottomCount + state.openWires.length) firstIndex == firstIndex))
              = false := by
            cases hSelf : (partnerIndexOf state.links
                (matchingBoundaryNodes bottomCount state)
                (bottomCount + state.openWires.length) firstIndex == firstIndex) with
            | true =>
                cases hAgree : (partnerIndexOf state.links
                    (matchingBoundaryNodes bottomCount state)
                    (bottomCount + state.openWires.length) firstIndex
                    == partnerIndexOf state.links
                      (matchingBoundaryNodes bottomCount state)
                      (bottomCount + state.openWires.length) secondIndex) with
                | true => rfl
                | false => rfl
            | false =>
                cases hAgree : (partnerIndexOf state.links
                    (matchingBoundaryNodes bottomCount state)
                    (bottomCount + state.openWires.length) firstIndex
                    == partnerIndexOf state.links
                      (matchingBoundaryNodes bottomCount state)
                      (bottomCount + state.openWires.length) secondIndex) with
                | false => rfl
                | true =>
                    have firstScanNe : findPartnerScan state.links
                        (matchingBoundaryNodes bottomCount state)
                        (unionFindRootOf state.links
                          (natListGetAt (matchingBoundaryNodes bottomCount state)
                            firstIndex))
                        firstIndex (List.range (bottomCount + state.openWires.length))
                        ≠ firstIndex :=
                      of_decide_eq_false hSelf
                    have soundFirst := findPartnerScan_root_ofFound state.links
                      (matchingBoundaryNodes bottomCount state)
                      (unionFindRootOf state.links
                        (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
                      firstIndex (List.range (bottomCount + state.openWires.length))
                      firstScanNe
                    have secondScanNe : findPartnerScan state.links
                        (matchingBoundaryNodes bottomCount state)
                        (unionFindRootOf state.links
                          (natListGetAt (matchingBoundaryNodes bottomCount state)
                            secondIndex))
                        secondIndex (List.range (bottomCount + state.openWires.length))
                        ≠ secondIndex := by
                      intro scanEq
                      have partnerFirstEq : partnerIndexOf state.links
                          (matchingBoundaryNodes bottomCount state)
                          (bottomCount + state.openWires.length) firstIndex
                          = secondIndex :=
                        (of_decide_eq_true hAgree).trans scanEq
                      have dTwoTrue : (partnerIndexOf state.links
                            (matchingBoundaryNodes bottomCount state)
                            (bottomCount + state.openWires.length) firstIndex
                          == secondIndex) = true :=
                        decide_eq_true partnerFirstEq
                      rw [dTwo] at dTwoTrue
                      exact Bool.noConfusion dTwoTrue
                    have soundSecond := findPartnerScan_root_ofFound state.links
                      (matchingBoundaryNodes bottomCount state)
                      (unionFindRootOf state.links
                        (natListGetAt (matchingBoundaryNodes bottomCount state)
                          secondIndex))
                      secondIndex (List.range (bottomCount + state.openWires.length))
                      secondScanNe
                    have scansEq : findPartnerScan state.links
                        (matchingBoundaryNodes bottomCount state)
                        (unionFindRootOf state.links
                          (natListGetAt (matchingBoundaryNodes bottomCount state)
                            firstIndex))
                        firstIndex (List.range (bottomCount + state.openWires.length))
                        = findPartnerScan state.links
                          (matchingBoundaryNodes bottomCount state)
                          (unionFindRootOf state.links
                            (natListGetAt (matchingBoundaryNodes bottomCount state)
                              secondIndex))
                          secondIndex
                          (List.range (bottomCount + state.openWires.length)) :=
                      of_decide_eq_true hAgree
                    rw [scansEq] at soundFirst
                    exact absurd (soundFirst.symm.trans soundSecond) rootsNe
          rw [dTwo, dThree, dFour]
          rfl

/-! ## The reconstruction -/

/-- ★ **Equal extracts yield the full connectivity-view simulation** — unconditionally.
Lengths and loops come from field congruence; the view agreement characterizes both sides as
partner-map views and rewrites the extract equality between them. -/
theorem matchingConnectivityViewSim_ofExtractEq (bottomCount : Nat)
    (stateT stateS : WireState)
    (extractsEqual : extractDiagram bottomCount stateT = extractDiagram bottomCount stateS) :
    MatchingConnectivityViewSim bottomCount stateT stateS := by
  have lengthEq : stateT.openWires.length = stateS.openWires.length :=
    congrArg DiagramType.topCount extractsEqual
  have loopsEq : stateT.loops = stateS.loops :=
    congrArg DiagramType.loops extractsEqual
  have viewAgrees : ∀ firstIndex secondIndex,
      firstIndex < bottomCount + stateS.openWires.length →
      secondIndex < bottomCount + stateS.openWires.length →
      matchingSameComponent bottomCount stateT firstIndex secondIndex
        = matchingSameComponent bottomCount stateS firstIndex secondIndex := by
    intro firstIndex secondIndex firstInRange secondInRange
    have firstInRangeT : firstIndex < bottomCount + stateT.openWires.length := by
      rw [lengthEq]
      exact firstInRange
    have secondInRangeT : secondIndex < bottomCount + stateT.openWires.length := by
      rw [lengthEq]
      exact secondInRange
    rw [matchingSameComponent_eq_diagramView bottomCount stateT firstIndex secondIndex
        firstInRangeT secondInRangeT,
      matchingSameComponent_eq_diagramView bottomCount stateS firstIndex secondIndex
        firstInRange secondInRange,
      extractsEqual]
  exact { lengthEq := lengthEq, loopsEq := loopsEq, viewAgrees := viewAgrees }

/-! ## Honesty marker -/

/-- **Honesty marker — the extract→view reconstruction is SHIPPED.**  The partner-map view
(`diagramSameComponentView`), the unconditional per-state characterization
(`matchingSameComponent_eq_diagramView`, via scan soundness / completeness / the
exclude-agreement trichotomy), and the reconstruction of the full
`MatchingConnectivityViewSim` from `extractDiagram` equality.  Together with
`extractDiagram_eq_of_connectivityView` the extract and the view are now INTERCHANGEABLE.
NOT yet covered: the run-composition law (equal `matchingOf` on a sub-cell transports through
the composite's remaining spine via the view-sim fold) inhabiting the
`MatchingSaturatedCongruence` fields — the closing MODE3-C brick.  `= true`. -/
def fxMode_hasMatchingExtractViewReconstruction : Bool := true

end FX1Poly.Polygraph
