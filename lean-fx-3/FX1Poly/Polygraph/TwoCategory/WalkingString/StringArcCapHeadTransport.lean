import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapHeadTransport
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcPairCapWindow
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowPartners
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapInternalCounts

/-! # WalkingString/StringArcCapHeadTransport — arc-structure equality locates the cap-head's realizing
atom, ported (FC-3 r20, THE CLONE CAMPAIGN — Branch B)

Phantom-signature two-token clone of the walking-adjunction `ArcCapHeadTransport`, re-plumbed onto the
FOUR-generator adjoint-triple seed.  When a CAP-HEADED reference spine and a second spine run from the
same seed have EQUAL full arc structures, the second spine contains a cap consuming exactly those two
seed ports adjacently — the `StringArcPairCapWindow` certificate.  The reference spine's extract values at
the window are shipped (the string `stringArcCapHeadFolded_windowLeftPartner` pins the partner read-off,
`stringArcCapHeadFolded_internalCapCountsCorr` pins the per-port cap counts to `[1, 1]`); structure
equality pushes both onto the second spine's extract, producing exactly the raw pins that
`stringArcPairCapWindow_ofFinalPins` consumes.  The private range plumbing is graph-neutral and
re-declared verbatim; the signature is a pure phantom, so ONLY the `SpineAtom`-quantified statement
clones.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range read plumbing (private copies — the seed files' kits are file-private) -/

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

private theorem natNeOfLt {smaller larger : Nat} (strict : smaller < larger) :
    smaller ≠ larger :=
  fun wouldBeEqual => absurd (wouldBeEqual ▸ strict) (Nat.lt_irrefl larger)

/-! ## The transport -/

/-- ★ **Arc-structure equality locates the cap-head's realizing atom**: a cap-headed
reference spine and a second spine from the same seed with EQUAL full arc structures force
the second spine to contain a cap consuming exactly the head's two seed ports adjacently. -/
theorem stringArcPairCapWindow_ofCapHeadExtractEq
    {firstSource firstTarget secondSource secondTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (firstTail : List (SpineAtom adjointTripleModeSignature firstSource firstTarget))
    (chained : SpineBoundaryChained tailBoundary firstTail)
    (secondAtoms : List (SpineAtom adjointTripleModeSignature secondSource secondTarget))
    (extractEq : extractArc bottomCount
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition)
          firstTail)
      = extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondAtoms)) :
    StringArcPairCapWindow bottomCount windowPosition (windowPosition + 1) secondAtoms := by
  have leftBelow : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have rightBelow : windowPosition + 1 < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (windowPosition + 1)) windowFits
  have firstRangeBound : windowPosition < (List.range (bottomCount
      + (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition)
        firstTail).openWires.length)).length := by
    rw [rangeLength]
    exact Nat.lt_of_lt_of_le leftBelow (Nat.le_add_right bottomCount _)
  have secondRangeBound : windowPosition < (List.range (bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondAtoms).openWires.length)).length := by
    rw [rangeLength]
    exact Nat.lt_of_lt_of_le leftBelow (Nat.le_add_right bottomCount _)
  have firstTotalBound : windowPosition < bottomCount
      + (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition)
        firstTail).openWires.length :=
    Nat.lt_of_lt_of_le leftBelow (Nat.le_add_right bottomCount _)
  have secondTotalBound : windowPosition < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondAtoms).openWires.length :=
    Nat.lt_of_lt_of_le leftBelow (Nat.le_add_right bottomCount _)
  -- the partner pin transported onto the second spine
  have partnerListsEq :
      (List.range (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition)
            firstTail).openWires.length)).map
        (partnerIndexOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition)
            firstTail).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition)
              firstTail).openWires)
          (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition)
              firstTail).openWires.length))
      = (List.range (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondAtoms).openWires.length)).map
        (partnerIndexOf
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondAtoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              secondAtoms).openWires)
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              secondAtoms).openWires.length)) :=
    congrArg (fun fullStructure => fullStructure.diagram.partner) extractEq
  have partnerReadsEq :
      natListGetAt
        ((List.range (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition)
              firstTail).openWires.length)).map
          (partnerIndexOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition)
              firstTail).links
            (List.range bottomCount
              ++ (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition)
                firstTail).openWires)
            (bottomCount
              + (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition)
                firstTail).openWires.length)))
        windowPosition
      = natListGetAt
          ((List.range (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                secondAtoms).openWires.length)).map
            (partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                secondAtoms).links
              (List.range bottomCount
                ++ (processArcSpine
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  secondAtoms).openWires)
              (bottomCount
                + (processArcSpine
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  secondAtoms).openWires.length)))
          windowPosition :=
    congrArg (fun wireList => natListGetAt wireList windowPosition) partnerListsEq
  have partnerPinSecond : partnerIndexOf
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondAtoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          secondAtoms).openWires)
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          secondAtoms).openWires.length)
      windowPosition
    = windowPosition + 1 := by
    rw [natListGetAt_map_inRange _ _ windowPosition firstRangeBound,
      natListGetAt_map_inRange _ _ windowPosition secondRangeBound,
      rangeGetAt_below _ windowPosition firstTotalBound,
      rangeGetAt_below _ windowPosition secondTotalBound] at partnerReadsEq
    rw [← partnerReadsEq]
    exact stringArcCapHeadFolded_windowLeftPartner bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits firstTail chained
  -- the count pin transported onto the second spine
  have countListsEq :
      (List.range (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition)
            firstTail).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition)
            firstTail).links
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition)
              firstTail).openWires)
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition)
            firstTail).capEventNodes)
      = (List.range (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondAtoms).openWires.length)).map
        (internalEventCountAt
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondAtoms).links
          (List.range bottomCount
            ++ (processArcSpine
              (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              secondAtoms).openWires)
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            secondAtoms).capEventNodes) :=
    congrArg FullArcStructure.internalCapCounts extractEq
  have countReadsEq :
      natListGetAt
        (natListInsertAt
          ((List.range
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  firstTail).openWires.length)).map
            (internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                firstTail).links
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  firstTail).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                firstTail).capEventNodes))
          windowPosition [1, 1])
        windowPosition
      = natListGetAt
          ((List.range (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                secondAtoms).openWires.length)).map
            (internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                secondAtoms).links
              (List.range bottomCount
                ++ (processArcSpine
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  secondAtoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                secondAtoms).capEventNodes))
          windowPosition := by
    rw [← stringArcCapHeadFolded_internalCapCountsCorr bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits firstTail chained]
    exact congrArg (fun wireList => natListGetAt wireList windowPosition) countListsEq
  have windowLeTailPorts : windowPosition
      ≤ ((List.range
          (tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              firstTail).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            firstTail).links
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              firstTail).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            firstTail).capEventNodes)).length := by
    rw [mapLength, rangeLength]
    have windowLeTailBoundary : windowPosition ≤ tailBoundary := by
      have shiftedFit : windowPosition + 2 ≤ tailBoundary + 2 := by
        rw [tailBoundaryFits]
        exact windowFits
      exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ shiftedFit)
    exact Nat.le_trans windowLeTailBoundary (Nat.le_add_right tailBoundary _)
  have countPinSecond : internalEventCountAt
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondAtoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          secondAtoms).openWires)
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        secondAtoms).capEventNodes
      windowPosition
    = 1 := by
    rw [natListGetAt_map_inRange _ _ windowPosition secondRangeBound,
      rangeGetAt_below _ windowPosition secondTotalBound] at countReadsEq
    rw [← countReadsEq]
    have insertRead := natListGetAt_natListInsertAt_inside
      ((List.range
          (tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              firstTail).openWires.length)).map
        (internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            firstTail).links
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              firstTail).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            firstTail).capEventNodes))
      windowPosition [1, 1] 0 (Nat.succ_pos 1) windowLeTailPorts
    rw [Nat.add_zero] at insertRead
    exact insertRead
  exact stringArcPairCapWindow_ofFinalPins bottomCount secondAtoms leftBelow rightBelow
    (natNeOfLt (Nat.lt_succ_self windowPosition)) partnerPinSecond countPinSecond

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-head pin transport, ported (FC-3 r20 clone campaign).**  Full-arc-structure
equality between a cap-headed reference spine and any second spine from the same seed transports the
reference's window values (partner = the adjacent port, strand cap count = one) onto the second spine's
extract and locates a cap in the second spine consuming exactly the head's two seed ports adjacently.
`= true`. -/
def fxString_hasArcCapHeadPinTransport : Bool := true

end FX1Poly.Polygraph
