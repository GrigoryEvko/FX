import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupScanAssembly

/-! # ArcCupPuncturedScan — off the fused component, the puncture is invisible

The cup-head punctured-scan analysis, OFF leg (peel campaign H, cup rung 2c).  The
composite partner scan is the JOINED-fresh scan over the punctured candidate range (cup
rung 2b); this brick shows that AWAY from the fused component the whole detour collapses:

  * `isSameComponent_unionFindJoin_offComponent` — a join is INVISIBLE to any query whose
    right probe sits outside both joined components: the joined view's answer is the base
    view's answer;
  * for an exclude read off both leg components, the two punctured-out leg candidates
    fail the PLAIN scan test (their reads are the leg nodes themselves), so restoring
    them to the candidate range changes nothing — and the joined links can be swapped for
    the plain links test-by-test;
  * ★ `arcCupHeadFolded_partnerScan_offFused` — therefore the PLAIN fresh `partnerIndexOf`
    at the two-zone shifted index IS the shift of the composite `partnerIndexOf`: away
    from the peeled cup's fused strand, the cup is transparent to the partner structure.

The fused component itself — where the puncture and the join both bite (the leg
rewiring) — is the next rung.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The join is invisible off the fused component -/

/-- ★ **Off-component join invisibility**: a `unionFindJoin` cannot change a
same-component query whose right probe lies outside BOTH joined components — the extra
disjuncts of the join characterization each carry a false conjunct. -/
theorem isSameComponent_unionFindJoin_offComponent (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight probeOne probeTwo : Nat)
    (offLeft : isSameComponent links joinLeft probeTwo = false)
    (offRight : isSameComponent links joinRight probeTwo = false) :
    isSameComponent (unionFindJoin links joinLeft joinRight) probeOne probeTwo
      = isSameComponent links probeOne probeTwo := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOne probeTwo,
    offLeft, offRight]
  cases baseTest : isSameComponent links probeOne probeTwo with
  | true =>
      cases legTest : isSameComponent links joinLeft probeOne with
      | true => rfl
      | false => rfl
  | false =>
      cases legTest : isSameComponent links joinLeft probeOne with
      | true => rfl
      | false => rfl

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

/-- Hand-rolled append associativity (the core lemma leaks `propext`). -/
private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

/-! ## Private scan plumbing -/

/-- Dropping two consecutive FAILING candidates anywhere in the list preserves the scan. -/
private theorem findPartnerScan_dropFailingPair (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex legLeft legRight : Nat)
    (leftFails : (legLeft != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes legLeft) == rootHere)
      = false)
    (rightFails : (legRight != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes legRight) == rootHere)
      = false) :
    (front tail : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex
        (front ++ legLeft :: legRight :: tail)
      = findPartnerScan links boundaryNodes rootHere excludeIndex (front ++ tail)
  | [], tail => by
      show findPartnerScan links boundaryNodes rootHere excludeIndex
          (legLeft :: legRight :: tail)
        = findPartnerScan links boundaryNodes rootHere excludeIndex tail
      rw [findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
          legLeft (legRight :: tail) leftFails,
        findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex
          legRight tail rightFails]
  | candidate :: frontRest, tail => by
      show findPartnerScan links boundaryNodes rootHere excludeIndex
          (candidate :: (frontRest ++ legLeft :: legRight :: tail))
        = findPartnerScan links boundaryNodes rootHere excludeIndex
            (candidate :: (frontRest ++ tail))
      rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
          (frontRest ++ legLeft :: legRight :: tail),
        findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate
          (frontRest ++ tail)]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => rfl
      | false =>
          show findPartnerScan links boundaryNodes rootHere excludeIndex
              (frontRest ++ legLeft :: legRight :: tail)
            = findPartnerScan links boundaryNodes rootHere excludeIndex (frontRest ++ tail)
          exact findPartnerScan_dropFailingPair links boundaryNodes rootHere excludeIndex
            legLeft legRight leftFails rightFails frontRest tail

/-- Two scans over the SAME candidates whose whole tests agree pointwise return the same
partner. -/
private theorem findPartnerScan_congrPointwise (linksLeft linksRight : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootLeft rootRight excludeIndex : Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates →
      (candidate != excludeIndex
          && unionFindRootOf linksLeft (natListGetAt boundaryNodes candidate) == rootLeft)
        = (candidate != excludeIndex
            && unionFindRootOf linksRight (natListGetAt boundaryNodes candidate)
              == rootRight)) →
    findPartnerScan linksLeft boundaryNodes rootLeft excludeIndex candidates
      = findPartnerScan linksRight boundaryNodes rootRight excludeIndex candidates
  | [], _ => rfl
  | candidate :: rest, pointwise => by
      rw [findPartnerScan_cons linksLeft boundaryNodes rootLeft excludeIndex candidate
          rest,
        findPartnerScan_cons linksRight boundaryNodes rootRight excludeIndex candidate
          rest,
        pointwise candidate (List.Mem.head rest)]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf linksRight (natListGetAt boundaryNodes candidate)
            == rootRight) with
      | true => rfl
      | false =>
          show findPartnerScan linksLeft boundaryNodes rootLeft excludeIndex rest
            = findPartnerScan linksRight boundaryNodes rootRight excludeIndex rest
          exact findPartnerScan_congrPointwise linksLeft linksRight boundaryNodes rootLeft
            rootRight excludeIndex rest
            (fun laterCandidate laterMem =>
              pointwise laterCandidate (List.Mem.tail candidate laterMem))

/-! ## The off-fused partner correspondence -/

/-- ★ **Off the fused component, the cup is transparent to the partner structure**: for a
composite exclude whose fresh boundary read sits outside BOTH leg components, the PLAIN
fresh `partnerIndexOf` at the two-zone shifted index equals the shift of the composite
`partnerIndexOf` — the punctured-out leg candidates fail the plain test (their reads are
the leg nodes), and the joined links agree with the plain links test-by-test by
off-component invisibility, so the whole cup rung 2b detour collapses. -/
theorem arcCupHeadFolded_partnerScan_offFused
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (compositeExclude : Nat)
    (excludeInRange : compositeExclude
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (offLeft : isSameComponent
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        windowPosition
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 compositeExclude)) = false)
    (offRight : isSameComponent
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (windowPosition + 1)
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 compositeExclude)) = false) :
    partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeExclude)
      = freshShiftAbove windowPosition 2
          (partnerIndexOf
            (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (List.range bottomCount
              ++ (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires)
            (bottomCount
              + (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires.length)
            compositeExclude) := by
  have windowLeTotal : windowPosition
      ≤ bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
    Nat.le_trans windowFits
      (Nat.le_add_right bottomCount
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowLeTotal
  have freshForest : isUnionFindForest
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links :=
    isUnionFindForest_processArcSpine atoms
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      isUnionFindForest_nil
  have legLeftBelowBlock : windowPosition < bottomCount + 2 :=
    Nat.lt_succ_of_le (Nat.le_succ_of_le windowFits)
  have legRightBelowBlock : windowPosition + 1 < bottomCount + 2 :=
    Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits)
  have readLegLeft : natListGetAt
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      windowPosition = windowPosition := by
    rw [natListGetAt_append_inside (List.range (bottomCount + 2))
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires
      windowPosition
      (by rw [rangeLength]; exact legLeftBelowBlock)]
    exact rangeGetAt_below (bottomCount + 2) windowPosition legLeftBelowBlock
  have readLegRight : natListGetAt
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (windowPosition + 1) = windowPosition + 1 := by
    rw [natListGetAt_append_inside (List.range (bottomCount + 2))
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires
      (windowPosition + 1)
      (by rw [rangeLength]; exact legRightBelowBlock)]
    exact rangeGetAt_below (bottomCount + 2) (windowPosition + 1) legRightBelowBlock
  have rootLeftFalse : (unionFindRootOf
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      windowPosition
      == unionFindRootOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 compositeExclude))) = false := offLeft
  have rootRightFalse : (unionFindRootOf
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (windowPosition + 1)
      == unionFindRootOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 compositeExclude))) = false := offRight
  have legLeftFails : ((windowPosition != freshShiftAbove windowPosition 2 compositeExclude)
      && (unionFindRootOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          windowPosition)
        == unionFindRootOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (freshShiftAbove windowPosition 2 compositeExclude)))) = false := by
    rw [readLegLeft, rootLeftFalse]
    cases bneValue : (windowPosition != freshShiftAbove windowPosition 2 compositeExclude)
      with
    | true => rfl
    | false => rfl
  have legRightFails : ((windowPosition + 1
        != freshShiftAbove windowPosition 2 compositeExclude)
      && (unionFindRootOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (windowPosition + 1))
        == unionFindRootOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (freshShiftAbove windowPosition 2 compositeExclude)))) = false := by
    rw [readLegRight, rootRightFalse]
    cases bneValue : (windowPosition + 1
        != freshShiftAbove windowPosition 2 compositeExclude) with
    | true => rfl
    | false => rfl
  have splitTotal : bottomCount + 2
      + (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires.length
    = windowPosition + 2 + tailCount :=
    (Nat.add_right_comm bottomCount 2
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length).trans
      ((congrArg (fun total => total + 2) tailSpec.symm).trans
        (Nat.add_right_comm windowPosition tailCount 2))
  have rangeEq : List.range
      (bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    = List.range windowPosition
        ++ windowPosition :: (windowPosition + 1)
          :: (List.range tailCount).map (fun offset => windowPosition + 2 + offset) := by
    rw [splitTotal, rangeInterleaveAtWindow windowPosition tailCount]
    exact appendAssoc (List.range windowPosition) [windowPosition, windowPosition + 1]
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset))
  have imageEq : List.range windowPosition
      ++ (List.range tailCount).map (fun offset => windowPosition + 2 + offset)
    = (List.range
        (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length)).map (freshShiftAbove windowPosition 2) :=
    (rangeMapShift_splitsAtWindow windowPosition tailCount).symm.trans
      (congrArg
        (fun total => (List.range total).map (freshShiftAbove windowPosition 2))
        tailSpec)
  have joinedCongr : findPartnerScan
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 compositeExclude)))
      (freshShiftAbove windowPosition 2 compositeExclude)
      ((List.range
        (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length)).map (freshShiftAbove windowPosition 2))
    = findPartnerScan
        (unionFindJoin
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          windowPosition (windowPosition + 1))
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (unionFindRootOf
          (unionFindJoin
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            windowPosition (windowPosition + 1))
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 compositeExclude)))
        (freshShiftAbove windowPosition 2 compositeExclude)
        ((List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)).map (freshShiftAbove windowPosition 2)) :=
    findPartnerScan_congrPointwise
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (unionFindJoin
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        windowPosition (windowPosition + 1))
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 compositeExclude)))
      (unionFindRootOf
        (unionFindJoin
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          windowPosition (windowPosition + 1))
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 compositeExclude)))
      (freshShiftAbove windowPosition 2 compositeExclude)
      ((List.range
        (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length)).map (freshShiftAbove windowPosition 2))
      (fun candidate _ =>
        congrArg
          (fun rootQuery =>
            ((candidate != freshShiftAbove windowPosition 2 compositeExclude)
              && rootQuery))
          (show (unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                      0 [] []) atoms).openWires)
                candidate)
              == unionFindRootOf
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                      0 [] []) atoms).links
                  (natListGetAt
                    (List.range (bottomCount + 2)
                      ++ (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).openWires)
                    (freshShiftAbove windowPosition 2 compositeExclude)))
            = (unionFindRootOf
                (unionFindJoin
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                      0 [] []) atoms).links
                  windowPosition (windowPosition + 1))
                (natListGetAt
                  (List.range (bottomCount + 2)
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) []
                        (bottomCount + 2) 0 [] []) atoms).openWires)
                  candidate)
                == unionFindRootOf
                    (unionFindJoin
                      (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).links
                      windowPosition (windowPosition + 1))
                    (natListGetAt
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      (freshShiftAbove windowPosition 2 compositeExclude)))
          from (isSameComponent_unionFindJoin_offComponent
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                [] []) atoms).links
            freshForest windowPosition (windowPosition + 1)
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              candidate)
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (freshShiftAbove windowPosition 2 compositeExclude))
            offLeft offRight).symm))
  show findPartnerScan
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 compositeExclude)))
      (freshShiftAbove windowPosition 2 compositeExclude)
      (List.range
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length))
    = freshShiftAbove windowPosition 2
        (partnerIndexOf
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                [] []) windowPosition) atoms).openWires)
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                [] []) windowPosition) atoms).openWires.length)
          compositeExclude)
  rw [rangeEq,
    findPartnerScan_dropFailingPair
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 compositeExclude)))
      (freshShiftAbove windowPosition 2 compositeExclude)
      windowPosition (windowPosition + 1) legLeftFails legRightFails
      (List.range windowPosition)
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    imageEq, joinedCongr]
  exact arcCupHeadFolded_partnerScanCorr bottomCount windowPosition windowFits atoms
    chained compositeExclude excludeInRange

/-! ## Honesty marker -/

/-- **Honesty marker — the punctured scan off the fused component (peel campaign H, cup
rung 2c).**  `isSameComponent_unionFindJoin_offComponent`: a join is invisible to queries
whose right probe sits outside both joined components.
`arcCupHeadFolded_partnerScan_offFused`: for composite excludes off both leg components,
the PLAIN fresh partner at the shifted index is the shift of the composite partner — the
punctured-out leg candidates fail the plain test and the join is invisible, so the cup is
transparent to the off-strand partner structure.  What this marker does NOT claim: the
FUSED-component analysis (the punctured scan for the leg-attachment probes — the leg
rewiring, where the join and the puncture both bite), the window-leg entries themselves,
and the assembled cup partner list.  `= true`. -/
def fxMode_hasArcCupOffFusedPartnerScan : Bool := true

end FX1Poly.Polygraph
