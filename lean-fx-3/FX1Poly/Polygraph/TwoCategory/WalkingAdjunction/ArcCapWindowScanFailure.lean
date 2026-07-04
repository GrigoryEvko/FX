import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSeedClosure
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentPersistence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCapWindowScanFailure — the consumed window pair fails every folded scan test

The cap-head partner-scan correspondence (peel campaign H, rung E-3, part 3a).  The
composite extract's candidate range carries two candidates the fresh extract never sees:
the window positions `windowPosition` and `windowPosition + 1`, whose boundary reads are
the consumed pair's own node ids.  The partner scan tests a candidate by comparing its
boundary node's component root against the root at a reindexed fresh node — and the
consumed pair can never pass: the left wire IS the strand-closure anchor, which misses
every reindexed probe (the seed-closure ride), and the right wire is linked to the left at
the seed and stays linked through the fold (component persistence), so the query transfers.
With both tests false, the interleave's middle segment drops out of the composite scan.

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

private theorem rangeLength (count : Nat) : (List.range count).length = count :=
  rangeLoopLength count []

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

private theorem andFalse_eq_false : (value : Bool) → (value && false) = false
  | true => rfl
  | false => rfl

/-! ## The two failing window tests -/

/-- **The left window candidate fails the folded scan test**: its boundary read is the
strand-closure anchor `windowPosition` itself, which misses every reindexed fresh probe at
the folded end state — so the exclude-and-root test is false against any σ-image root. -/
theorem arcCapHeadFolded_windowLeftScanTestFails
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms)
    (topWires : List Nat) (excludeIndex anchorProbe : Nat) :
    (windowPosition != excludeIndex
        && unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt (List.range bottomCount ++ topWires) windowPosition)
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
                anchorProbe))
      = false := by
  have leftBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have boundaryRead : natListGetAt (List.range bottomCount ++ topWires) windowPosition
      = windowPosition := by
    rw [natListGetAt_append_inside (List.range bottomCount) topWires windowPosition
      (by rw [rangeLength]; exact leftBelowBoundary)]
    exact rangeGetAt_below bottomCount windowPosition leftBelowBoundary
  have rootsMiss : (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links windowPosition
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
              anchorProbe)) = false :=
    arcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits atoms chained anchorProbe
  rw [boundaryRead, rootsMiss]
  exact andFalse_eq_false (windowPosition != excludeIndex)

/-- **The right window candidate fails the folded scan test**: its boundary read is the
consumed right wire `windowPosition + 1`, which is linked to the anchor at the seed and
stays linked through the fold — so its component query transfers to the anchor's, which
misses every reindexed fresh probe. -/
theorem arcCapHeadFolded_windowRightScanTestFails
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms)
    (topWires : List Nat) (excludeIndex anchorProbe : Nat) :
    ((windowPosition + 1) != excludeIndex
        && unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt (List.range bottomCount ++ topWires) (windowPosition + 1))
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
                anchorProbe))
      = false := by
  have boundaryRead : natListGetAt (List.range bottomCount ++ topWires) (windowPosition + 1)
      = windowPosition + 1 := by
    rw [natListGetAt_append_inside (List.range bottomCount) topWires (windowPosition + 1)
      (by rw [rangeLength]; exact windowFits)]
    exact rangeGetAt_below bottomCount (windowPosition + 1) windowFits
  have pairLinked : isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      windowPosition (windowPosition + 1) = true :=
    arcCapHeadFolded_consumedPairLinked bottomCount windowPosition windowFits atoms
  have queryTransfer := isSameComponent_congrOfLinked
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).links
    windowPosition (windowPosition + 1)
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      anchorProbe)
    pairLinked
  have rootsMiss : (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links (windowPosition + 1)
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
              anchorProbe)) = false :=
    queryTransfer.symm.trans
      (arcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained anchorProbe)
  rw [boundaryRead, rootsMiss]
  exact andFalse_eq_false ((windowPosition + 1) != excludeIndex)

/-! ## The packaged middle-segment hypothesis -/

/-- ★ **The consumed window pair fails every folded scan test** — packaged in exactly the
shape `findPartnerScan_dropMiddle_ofAllFail` consumes: both middle candidates' tests are
false against any σ-image root, so the interleave's window segment drops out of the
composite scan. -/
theorem arcCapHeadFolded_windowPairScanTestsFail
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms)
    (topWires : List Nat) (excludeIndex anchorProbe : Nat) :
    ∀ candidate, candidate ∈ [windowPosition, windowPosition + 1] →
    (candidate != excludeIndex
        && unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt (List.range bottomCount ++ topWires) candidate)
          == unionFindRootOf
              (processArcSpine
                (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
                anchorProbe))
      = false := by
  intro candidate candidateMem
  cases candidateMem with
  | head =>
      exact arcCapHeadFolded_windowLeftScanTestFails bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained topWires excludeIndex anchorProbe
  | tail _ restMem =>
      cases restMem with
      | head =>
          exact arcCapHeadFolded_windowRightScanTestFails bottomCount windowPosition
            tailBoundary windowFits tailBoundaryFits atoms chained topWires excludeIndex
            anchorProbe
      | tail _ nilMem => nomatch nilMem

/-! ## Honesty marker -/

/-- **Honesty marker — the consumed window pair fails every folded scan test (peel
campaign H, rung E-3, part 3a).**  At the cap-head folded end state, both window
candidates' exclude-and-root tests are false against any reindexed-fresh-probe root: the
left wire is the strand-closure anchor (seed-closure miss), the right wire transfers its
query to the anchor through the persistent consumed-pair link.  Packaged as the
`dropMiddle` middle-fails hypothesis.  What this marker does NOT claim: the per-candidate
test correspondence between the composite and fresh scans at the shift-image candidates,
and the assembled scan/partner/diagram equality.  `= true`. -/
def fxMode_hasArcCapWindowScanFailure : Bool := true

end FX1Poly.Polygraph
