import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadStructure
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCountCancellation

/-! # ArcCupTransportReadoff — the composite equality read off POINTWISE (peel campaign H, parity rung P-5c)

The cup-head correspondences state the composite extract's fields as MAPPED transports of
the fresh run data; the mixed-cell analysis of the partner cancel needs those transports
POINTWISE — one equation per composite index, on each field separately.  This brick reads
them off: project the composite extract equality at a field, rewrite both sides through
that field's correspondence, align the boundary ranges by the width cancel, and read the
map equality at every member.  Field-by-field projection keeps the hypotheses honest: the
partner leg needs the legs-separate discipline (its correspondence's precondition), the
two internal-count legs need only the chain discipline — and NO leg needs the window
parity (that was only ever the loops leg's precondition).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopMem_ofAccumulated : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target ∈ accumulated → target ∈ List.range.loop count accumulated
  | 0, _, _, targetMem => targetMem
  | count + 1, accumulated, target, targetMem =>
      rangeLoopMem_ofAccumulated count (count :: accumulated) target
        (List.Mem.tail count targetMem)

private theorem rangeLoopMem_ofLt : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target < count → target ∈ List.range.loop count accumulated
  | 0, _, target, targetBelow => absurd targetBelow (Nat.not_lt_zero target)
  | count + 1, accumulated, target, targetBelow => by
      cases Nat.lt_or_ge target count with
      | inl below => exact rangeLoopMem_ofLt count (count :: accumulated) target below
      | inr atLeast =>
          have targetEq : target = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ targetBelow) atLeast
          rw [targetEq]
          exact rangeLoopMem_ofAccumulated count (count :: accumulated) count
            (List.Mem.head accumulated)

private theorem rangeMem_ofLt (count target : Nat) (targetBelow : target < count) :
    target ∈ List.range count :=
  rangeLoopMem_ofLt count [] target targetBelow

/-- Equal mapped lists agree at every member — the read-off inverse of `listMapCongr`. -/
private theorem mapAgree_onMembers {firstValue secondValue : Nat → Nat} :
    (positions : List Nat) →
    positions.map firstValue = positions.map secondValue →
    ∀ position : Nat, position ∈ positions → firstValue position = secondValue position
  | [], _, _, positionMem => nomatch positionMem
  | head :: rest, mapsEqual, position, positionMem => by
      have consEqual : firstValue head :: rest.map firstValue
          = secondValue head :: rest.map secondValue := mapsEqual
      injection consEqual with headEqual restEqual
      cases positionMem with
      | head => exact headEqual
      | tail _ restMem => exact mapAgree_onMembers rest restEqual position restMem

/-! ## The partner transport, pointwise -/

/-- ★ **Equal composite extracts read off the partner transport POINTWISE**: at every
in-range composite index the two runs' `arcCupPartnerTransport` values coincide.  Projects
the composite equality at the partner field, rewrites through the partner-list
correspondence on both sides (the legs-separate discipline is its precondition), aligns
the ranges by the width cancel, and reads the map equality at the member. -/
theorem arcCupHeadFolded_partnerTransport_pointwise
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained (bottomCount + 2) firstAtoms)
    (secondChained : SpineBoundaryChained (bottomCount + 2) secondAtoms)
    (firstLegsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).links windowPosition (windowPosition + 1) = false)
    (secondLegsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        secondAtoms).links windowPosition (windowPosition + 1) = false)
    (compositeEq : extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms))
    (compositeIndex : Nat)
    (indexInRange : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length) :
    arcCupPartnerTransport
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length)
        windowPosition compositeIndex
      = arcCupPartnerTransport
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires.length)
          windowPosition compositeIndex := by
  have widthEq := arcCupHeadFolded_topCount_cancel bottomCount windowPosition
    firstAtoms secondAtoms compositeEq
  have rangeBoundEq : bottomCount
      + (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).openWires.length
    = bottomCount
      + (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        secondAtoms).openWires.length :=
    congrArg (fun topWidth => bottomCount + topWidth) widthEq
  have partnerListsEqual : (List.range
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms).openWires.length)).map
      (partnerIndexOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms).openWires.length))
      = (List.range
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms).openWires.length)).map
        (partnerIndexOf
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms).openWires)
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms).openWires.length)) :=
    congrArg (fun arcData => arcData.diagram.partner) compositeEq
  rw [arcCupHeadFolded_partnerListCorr bottomCount windowPosition windowFits firstAtoms
      firstChained firstLegsSeparate,
    arcCupHeadFolded_partnerListCorr bottomCount windowPosition windowFits secondAtoms
      secondChained secondLegsSeparate,
    ← rangeBoundEq] at partnerListsEqual
  exact mapAgree_onMembers
    (List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length))
    partnerListsEqual compositeIndex
    (rangeMem_ofLt
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length)
      compositeIndex indexInRange)

/-! ## The internal-count transports, pointwise -/

/-- ★ **Equal composite extracts read off the internal CUP-count transport POINTWISE** —
at every in-range composite index the two runs' leg-joined fresh cup censuses (with the
head's own event) coincide.  Only the chain discipline is needed: the count
correspondence covers the cup-cancel world. -/
theorem arcCupHeadFolded_cupCountTransport_pointwise
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained (bottomCount + 2) firstAtoms)
    (secondChained : SpineBoundaryChained (bottomCount + 2) secondAtoms)
    (compositeEq : extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms))
    (compositeIndex : Nat)
    (indexInRange : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length) :
    arcCupCountTransport
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).cupEventNodes
        windowPosition 1 compositeIndex
      = arcCupCountTransport
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).cupEventNodes
          windowPosition 1 compositeIndex := by
  have widthEq := arcCupHeadFolded_topCount_cancel bottomCount windowPosition
    firstAtoms secondAtoms compositeEq
  have rangeBoundEq : bottomCount
      + (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).openWires.length
    = bottomCount
      + (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        secondAtoms).openWires.length :=
    congrArg (fun topWidth => bottomCount + topWidth) widthEq
  have countListsEqual : (List.range
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms).openWires.length)).map
      (internalEventCountAt
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms).openWires)
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms).cupEventNodes)
      = (List.range
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms).openWires)
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms).cupEventNodes) :=
    congrArg FullArcStructure.internalCupCounts compositeEq
  rw [arcCupHeadFolded_internalCupCountsCorr bottomCount windowPosition windowFits
      firstAtoms firstChained,
    arcCupHeadFolded_internalCupCountsCorr bottomCount windowPosition windowFits
      secondAtoms secondChained,
    ← rangeBoundEq] at countListsEqual
  exact mapAgree_onMembers
    (List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length))
    countListsEqual compositeIndex
    (rangeMem_ofLt
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length)
      compositeIndex indexInRange)

/-- ★ **Equal composite extracts read off the internal CAP-count transport POINTWISE** —
the mirror at the cap-event census, with no head contribution. -/
theorem arcCupHeadFolded_capCountTransport_pointwise
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained (bottomCount + 2) firstAtoms)
    (secondChained : SpineBoundaryChained (bottomCount + 2) secondAtoms)
    (compositeEq : extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms))
    (compositeIndex : Nat)
    (indexInRange : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length) :
    arcCupCountTransport
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).capEventNodes
        windowPosition 0 compositeIndex
      = arcCupCountTransport
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).capEventNodes
          windowPosition 0 compositeIndex := by
  have widthEq := arcCupHeadFolded_topCount_cancel bottomCount windowPosition
    firstAtoms secondAtoms compositeEq
  have rangeBoundEq : bottomCount
      + (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).openWires.length
    = bottomCount
      + (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        secondAtoms).openWires.length :=
    congrArg (fun topWidth => bottomCount + topWidth) widthEq
  have countListsEqual : (List.range
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms).openWires.length)).map
      (internalEventCountAt
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) firstAtoms).openWires)
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms).capEventNodes)
      = (List.range
          (bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) secondAtoms).openWires)
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms).capEventNodes) :=
    congrArg FullArcStructure.internalCapCounts compositeEq
  rw [arcCupHeadFolded_internalCapCountsCorr bottomCount windowPosition windowFits
      firstAtoms firstChained,
    arcCupHeadFolded_internalCapCountsCorr bottomCount windowPosition windowFits
      secondAtoms secondChained,
    ← rangeBoundEq] at countListsEqual
  exact mapAgree_onMembers
    (List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length))
    countListsEqual compositeIndex
    (rangeMem_ofLt
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length)
      compositeIndex indexInRange)

/-! ## Honesty marker -/

/-- **Honesty marker — the pointwise transport read-off is SHIPPED (peel campaign H,
parity rung P-5c).**  Equal composite cup-head extracts read off, at every in-range
composite index, the partner transport (`arcCupHeadFolded_partnerTransport_pointwise` —
under the legs-separate discipline) and the two internal-count transports
(`arcCupHeadFolded_cupCountTransport_pointwise` /
`arcCupHeadFolded_capCountTransport_pointwise` — under the chain discipline alone), with
no window-parity hypothesis anywhere.  What this marker does NOT claim: the fresh partner
cancel over these pointwise equations (the mixed fused/off-leg cells — where the count
transports join the fight), the cup-front locate, and the orbit-realignment endgame.
`= true`. -/
def fxMode_hasArcCupTransportReadoff : Bool := true

end FX1Poly.Polygraph
