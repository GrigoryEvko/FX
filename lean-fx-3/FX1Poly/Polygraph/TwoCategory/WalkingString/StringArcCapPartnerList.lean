import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapPartnerList
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapBoundaryReads
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapScanAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowPartners

/-! # WalkingString/StringArcCapPartnerList — the composite partner list is the spliced shift-image,
ported (FC-3 r20, THE CLONE CAMPAIGN — Branch A)

Phantom-signature two-token clone of the walking-adjunction `ArcCapPartnerList`, re-plumbed onto the
FOUR-generator adjoint-triple seed.  The composite extract's whole partner list equals the fresh
extract's partner list transported by the two-zone index shift with the consumed window pair
`[windowPosition + 1, windowPosition]` spliced in at the window: below-window entries are shift-images
of fresh partners (the string scan correspondence `stringArcCapHeadFolded_partnerScanCorr` at fixed
indices), the two window entries partner each other (the string window-partner bricks
`stringArcCapHeadFolded_window{Left,Right}Partner`), and past-window entries are shift-images at
shifted indices.  The private list-factorization kit is graph-neutral and re-declared verbatim; the
signature is a pure phantom, so ONLY the `SpineAtom`-quantified statements clone.

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

/-- Hand-rolled append associativity (the core lemma leaks `propext`). -/
private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

/-- Inserting a block exactly at the front segment's length splices it between the
segments. -/
private theorem natListInsertAt_splitsAtLength : (front : List Nat) → (position : Nat) →
    (back block : List Nat) → front.length = position →
    natListInsertAt (front ++ back) position block = front ++ (block ++ back)
  | [], position, back, block, lengthEq => by
      cases lengthEq
      cases back with
      | nil => exact rfl
      | cons headWire restWires => exact rfl
  | headWire :: frontRest, position, back, block, lengthEq => by
      cases lengthEq
      show headWire :: natListInsertAt (frontRest ++ back) frontRest.length block
        = headWire :: (frontRest ++ (block ++ back))
      exact congrArg (fun spliced => headWire :: spliced)
        (natListInsertAt_splitsAtLength frontRest frontRest.length back block rfl)

/-- A map whose every entry factors through a shifted base read IS the double map:
pointwise factorization gives the list-level factorization (structural recursion — no
`funext`, no fused-lambda beta redexes). -/
private theorem listMapFactorsThroughShift
    (compositeRead freshRead indexShift : Nat → Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates →
      compositeRead candidate = indexShift (freshRead candidate)) →
    candidates.map compositeRead = (candidates.map freshRead).map indexShift
  | [], _ => rfl
  | headCandidate :: rest, pointwise => by
      show compositeRead headCandidate :: rest.map compositeRead
        = indexShift (freshRead headCandidate) :: (rest.map freshRead).map indexShift
      rw [pointwise headCandidate (List.Mem.head rest),
        listMapFactorsThroughShift compositeRead freshRead indexShift rest
          (fun laterCandidate laterMem =>
            pointwise laterCandidate (List.Mem.tail headCandidate laterMem))]

/-- The past-window variant: composite reads at `windowPosition + 2 + offset` factor
through fresh reads at `windowPosition + offset` — the two offset spellings are baked into
the statement so no fused-lambda rewriting is ever needed. -/
private theorem listMapPastWindowFactors
    (compositeRead freshRead indexShift : Nat → Nat) (windowPosition : Nat) :
    (offsets : List Nat) →
    (∀ offset, offset ∈ offsets →
      compositeRead (windowPosition + 2 + offset)
        = indexShift (freshRead (windowPosition + offset))) →
    (offsets.map (fun offset => windowPosition + 2 + offset)).map compositeRead
      = ((offsets.map (fun offset => windowPosition + offset)).map freshRead).map
          indexShift
  | [], _ => rfl
  | headOffset :: rest, pointwise => by
      show compositeRead (windowPosition + 2 + headOffset)
          :: (rest.map (fun offset => windowPosition + 2 + offset)).map compositeRead
        = indexShift (freshRead (windowPosition + headOffset))
          :: ((rest.map (fun offset => windowPosition + offset)).map freshRead).map
              indexShift
      rw [pointwise headOffset (List.Mem.head rest),
        listMapPastWindowFactors compositeRead freshRead indexShift windowPosition rest
          (fun laterOffset laterMem =>
            pointwise laterOffset (List.Mem.tail headOffset laterMem))]

/-! ## The assembled partner-list correspondence -/

/-- ★ **The composite partner list is the spliced shift-image of the fresh partner list**:
at the cap-head folded end state, the whole boundary partner list equals the fresh partner
list mapped through the two-zone index shift, with the window pair `[windowPosition + 1,
windowPosition]` inserted at the window position.  Below-window and past-window entries
ride the assembled partner-scan correspondence at fixed and shifted indices respectively;
the window pair rides the window-partner brick. -/
theorem stringArcCapHeadFolded_partnerListCorr
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    (List.range
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)).map
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      = natListInsertAt
          (((List.range
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length)).map
            (partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires)
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length))).map
            (freshShiftAbove windowPosition 2))
          windowPosition
          [windowPosition + 1, windowPosition] := by
  have windowLeTail : windowPosition ≤ tailBoundary := by
    have paddedLe : windowPosition + 2 ≤ tailBoundary + 2 := by
      rw [tailBoundaryFits]
      exact windowFits
    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ paddedLe)
  have windowLeTotal : windowPosition
      ≤ tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
    Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowLeTotal
  have compositeCandidatesEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      = List.range ((windowPosition + 2) + tailCount) :=
    congrArg List.range
      ((stringArcCapHeadFolded_totalPorts bottomCount windowPosition tailBoundary windowFits
          tailBoundaryFits atoms).trans
        ((congrArg (fun totalPorts => totalPorts + 2) tailSpec.symm).trans
          (Nat.add_right_comm windowPosition tailCount 2)))
  have freshCandidatesSplitEq : List.range
      (tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
      = List.range windowPosition
          ++ (List.range tailCount).map (fun offset => windowPosition + offset) :=
    (congrArg List.range tailSpec.symm).trans (rangeSplit windowPosition tailCount)
  have belowSegEq : (List.range windowPosition).map
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      = ((List.range windowPosition).map
          (partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            (tailBoundary
              + (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires.length))).map
          (freshShiftAbove windowPosition 2) :=
    listMapFactorsThroughShift
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      (partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).links
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        (tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length))
      (freshShiftAbove windowPosition 2)
      (List.range windowPosition)
      (fun candidate candidateMem => by
        have candidateBelow : candidate < windowPosition :=
          mem_range_imp_lt candidateMem
        have shiftFixed : freshShiftAbove windowPosition 2 candidate = candidate :=
          freshShiftAbove_ofNotLe windowPosition 2 candidate
            (fun windowLe =>
              Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe candidateBelow))
        have corrShifted : partnerIndexOf
            (processArcSpine
              (stepCapArc
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (List.range bottomCount
              ++ (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires)
            (bottomCount
              + (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires.length)
            (freshShiftAbove windowPosition 2 candidate)
            = freshShiftAbove windowPosition 2
              (partnerIndexOf
                (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).links
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                (tailBoundary
                  + (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires.length)
                candidate) :=
          stringArcCapHeadFolded_partnerScanCorr bottomCount windowPosition tailBoundary
            windowFits tailBoundaryFits atoms chained candidate
            (Nat.lt_of_lt_of_le candidateBelow windowLeTotal)
        rw [shiftFixed] at corrShifted
        exact corrShifted)
  have pastSegEq : ((List.range tailCount).map
        (fun offset => windowPosition + 2 + offset)).map
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      = (((List.range tailCount).map (fun offset => windowPosition + offset)).map
          (partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            (tailBoundary
              + (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires.length))).map
          (freshShiftAbove windowPosition 2) :=
    listMapPastWindowFactors
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      (partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).links
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        (tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length))
      (freshShiftAbove windowPosition 2)
      windowPosition
      (List.range tailCount)
      (fun offset offsetMem => by
        have offsetBelow : offset < tailCount := mem_range_imp_lt offsetMem
        have excludeInRange : windowPosition + offset
            < tailBoundary
              + (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires.length := by
          have shifted : windowPosition + offset < windowPosition + tailCount :=
            Nat.add_lt_add_left offsetBelow windowPosition
          rw [tailSpec] at shifted
          exact shifted
        have shiftPast : freshShiftAbove windowPosition 2 (windowPosition + offset)
            = windowPosition + offset + 2 :=
          freshShiftAbove_ofLe windowPosition 2 (windowPosition + offset)
            (Nat.le_add_right windowPosition offset)
        have corrShifted : partnerIndexOf
            (processArcSpine
              (stepCapArc
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (List.range bottomCount
              ++ (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires)
            (bottomCount
              + (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires.length)
            (freshShiftAbove windowPosition 2 (windowPosition + offset))
            = freshShiftAbove windowPosition 2
              (partnerIndexOf
                (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).links
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                (tailBoundary
                  + (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires.length)
                (windowPosition + offset)) :=
          stringArcCapHeadFolded_partnerScanCorr bottomCount windowPosition tailBoundary
            windowFits tailBoundaryFits atoms chained (windowPosition + offset)
            excludeInRange
        rw [shiftPast, Nat.add_right_comm windowPosition offset 2] at corrShifted
        exact corrShifted)
  have windowSegEq : ([windowPosition, windowPosition + 1]).map
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      = [windowPosition + 1, windowPosition] := by
    show partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)
        windowPosition
      :: partnerIndexOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length)
          (windowPosition + 1)
      :: [] = [windowPosition + 1, windowPosition]
    rw [stringArcCapHeadFolded_windowLeftPartner bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained,
      stringArcCapHeadFolded_windowRightPartner bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained]
  have frontLengthEq : (((List.range windowPosition).map
      (partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).links
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        (tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length))).map
      (freshShiftAbove windowPosition 2)).length = windowPosition :=
    (mapLength (freshShiftAbove windowPosition 2)
        ((List.range windowPosition).map
          (partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            (tailBoundary
              + (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires.length)))).trans
      ((mapLength
          (partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            (tailBoundary
              + (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires.length))
          (List.range windowPosition)).trans
        (rangeLength windowPosition))
  rw [compositeCandidatesEq, rangeInterleaveAtWindow windowPosition tailCount,
    mapAppend
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      (List.range windowPosition ++ [windowPosition, windowPosition + 1])
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    mapAppend
      (partnerIndexOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length))
      (List.range windowPosition) [windowPosition, windowPosition + 1],
    freshCandidatesSplitEq,
    mapAppend
      (partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).links
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        (tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length))
      (List.range windowPosition)
      ((List.range tailCount).map (fun offset => windowPosition + offset)),
    mapAppend (freshShiftAbove windowPosition 2)
      ((List.range windowPosition).map
        (partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          (tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires.length)))
      (((List.range tailCount).map (fun offset => windowPosition + offset)).map
        (partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          (tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires.length))),
    natListInsertAt_splitsAtLength
      (((List.range windowPosition).map
        (partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          (tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires.length))).map
        (freshShiftAbove windowPosition 2))
      windowPosition
      ((((List.range tailCount).map (fun offset => windowPosition + offset)).map
        (partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          (tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires.length))).map
        (freshShiftAbove windowPosition 2))
      [windowPosition + 1, windowPosition]
      frontLengthEq,
    belowSegEq, windowSegEq, pastSegEq]
  exact appendAssoc
    (((List.range windowPosition).map
      (partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).links
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        (tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length))).map
      (freshShiftAbove windowPosition 2))
    [windowPosition + 1, windowPosition]
    ((((List.range tailCount).map (fun offset => windowPosition + offset)).map
      (partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).links
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        (tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length))).map
      (freshShiftAbove windowPosition 2))

/-! ## Honesty marker -/

/-- **Honesty marker — the composite partner list is the spliced shift-image, ported (FC-3 r20 clone
campaign).**  At the cap-head folded end state, the composite extract's whole partner list equals
`natListInsertAt (freshPartnerList.map shift) windowPosition [windowPosition + 1, windowPosition]`:
below/past-window entries ride the assembled partner-scan correspondence, the window pair rides the
window-partner bricks, and the splice rides the insert-at-front-length decomposition.  What this marker
does NOT claim: the assembled `DiagramType` equality and the full `FullArcStructure` cap-head transport.
`= true`. -/
def fxString_hasArcCapPartnerList : Bool := true

end FX1Poly.Polygraph
