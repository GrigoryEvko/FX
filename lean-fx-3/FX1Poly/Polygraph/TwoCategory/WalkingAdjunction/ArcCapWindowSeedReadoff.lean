import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPrefixBubbleDescent
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairCapWindow

/-! # ArcCapWindowSeedReadoff — the located cap bubbles to the front, pinned at the seed

The witness campaign's read-off: an `ArcPairCapWindow` certificate over a boundary-chained
spine feeds the prefix descent master at the CANONICAL SEED, and the seed's range reads pin
the outcome — the located cap bubbles to the front as an atom whose window is EXACTLY the
certificate's window position and whose source boundary is EXACTLY the seed width.

Two seed facts close the argument: the pair's seat in the seed state reads off the range
(`natListGetAt` on `List.range` is the identity below the width), so the moved window IS the
left pinned port; and the certificate's swapped-order branch is IMPOSSIBLE at the seed — it
would force `windowPosition + 2 = windowPosition`.  The chain discipline advances along the
arc fold (`spineBoundaryChained_alongArcSpine`) to produce the split-state seat bound the
master consumes, and the bubbled list's own chaining pins the moved atom's source boundary.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

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

/-! ## The chain discipline advances along the arc fold -/

/-- The boundary chain survives folding a spine segment: chained at the entry state's
open-wire count, the remainder is chained at the advanced state's — each cup/cap step tracks
its boundary (`stepArcAtom_openWires_tracksBoundary`), and every walking-adjunction atom has
the required arity. -/
theorem spineBoundaryChained_alongArcSpine
    {sourceMode targetMode : adjunctionGraph.Mode} :
    (atoms rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode)) →
    (state : ArcWireState) →
    SpineBoundaryChained state.openWires.length (atoms ++ rest) →
    SpineBoundaryChained (processArcSpine state atoms).openWires.length rest
  | [], _, _, chained => chained
  | headAtom :: tailAtoms, rest, state, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      rw [← stepArcAtom_openWires_tracksBoundary state headAtom
        (adjunctionSpineAtom_hasCupOrCapArity headAtom) headFires.symm] at tailChained
      exact spineBoundaryChained_alongArcSpine tailAtoms rest (stepArcAtom state headAtom)
        tailChained

/-! ## The read-off -/

/-- ★ **The located cap bubbles to the front, pinned at the seed.**  Over a boundary-chained
walking-adjunction spine, the `ArcPairCapWindow` certificate at the pinned ports
`windowPosition, windowPosition + 1` yields the split together with a bubble witness whose
moved atom is a cap firing at EXACTLY `windowPosition` on EXACTLY the seed boundary — the
head-identification data.  The certificate's swapped-order branch dies at the seed (it would
force the window position to wrap). -/
theorem bubblesToFront_ofArcPairCapWindow (bottomCount windowPosition : Nat)
    {sourceMode targetMode : adjunctionGraph.Mode}
    (secondAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (chainedSecond : SpineBoundaryChained bottomCount secondAtoms)
    (located : ArcPairCapWindow bottomCount windowPosition (windowPosition + 1)
      secondAtoms) :
    ∃ (prefixAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
      (toucherAtom : SpineAtom adjunctionModeSignature sourceMode targetMode)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
      (movedTarget : SpineAtom adjunctionModeSignature sourceMode targetMode)
      (movedPrefixAtoms :
        List (SpineAtom adjunctionModeSignature sourceMode targetMode)),
      secondAtoms = prefixAtoms ++ toucherAtom :: suffixAtoms
        ∧ BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 2
        ∧ movedTarget.generatorCod.length = 0
        ∧ movedTarget.leftContext.length = windowPosition
        ∧ movedTarget.domBoundaryLength = bottomCount := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, doesSplitSpine, _, hasCapDomArity,
    hasCapCodArity, doesConsumePair⟩ := located
  rw [doesSplitSpine] at chainedSecond
  have chainedAtSeed : SpineBoundaryChained
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires.length
      (prefixAtoms ++ toucherAtom :: suffixAtoms) := by
    show SpineBoundaryChained (List.range bottomCount).length
      (prefixAtoms ++ toucherAtom :: suffixAtoms)
    rw [rangeLength bottomCount]
    exact chainedSecond
  have chainedAtSplit : SpineBoundaryChained
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).openWires.length
      (toucherAtom :: suffixAtoms) :=
    spineBoundaryChained_alongArcSpine prefixAtoms (toucherAtom :: suffixAtoms)
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) chainedAtSeed
  have splitEntryShape : (processArcSpine
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      prefixAtoms).openWires.length
      = toucherAtom.leftContext.length + toucherAtom.generatorDom.length
        + toucherAtom.rightContext.length :=
    (spineBoundaryChained_tail chainedAtSplit).1.symm
  have seatBound : toucherAtom.leftContext.length + 2
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).openWires.length := by
    rw [splitEntryShape, hasCapDomArity]
    exact Nat.le_add_right (toucherAtom.leftContext.length + 2)
      toucherAtom.rightContext.length
  have windowBelowBottom : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  cases doesConsumePair with
  | inl orderedReads =>
      obtain ⟨movedTarget, movedPrefixAtoms, witness, movedDomPin, movedCodPin, seatedSeed,
        _⟩ :=
        arcPairSeated_bubblesThroughPrefix toucherAtom hasCapDomArity hasCapCodArity
          suffixAtoms windowPosition (windowPosition + 1) prefixAtoms
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowBelowBottom windowFits chainedAtSeed
          ⟨orderedReads.1, orderedReads.2, seatBound⟩
      have seatWindowBound : movedTarget.leftContext.length + 2
          ≤ (List.range bottomCount).length := seatedSeed.2.2
      rw [rangeLength bottomCount] at seatWindowBound
      have seatBelowBottom : movedTarget.leftContext.length < bottomCount :=
        Nat.lt_of_lt_of_le
          (Nat.lt_trans (Nat.lt_succ_self movedTarget.leftContext.length)
            (Nat.lt_succ_self (movedTarget.leftContext.length + 1)))
          seatWindowBound
      have leftSeatRead : natListGetAt (List.range bottomCount)
          movedTarget.leftContext.length = windowPosition := seatedSeed.1
      have windowPin : movedTarget.leftContext.length = windowPosition :=
        (rangeGetAt_below bottomCount movedTarget.leftContext.length
          seatBelowBottom).symm.trans leftSeatRead
      have bubbledChained : SpineBoundaryChained
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []).openWires.length
          (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) :=
        spineBoundaryChained_of_bubblesToFront witness suffixAtoms chainedAtSeed
      have boundaryPinRaw : movedTarget.domBoundaryLength
          = (List.range bottomCount).length :=
        (spineBoundaryChained_tail bubbledChained).1
      exact ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
        doesSplitSpine, witness, movedDomPin, movedCodPin, windowPin,
        boundaryPinRaw.trans (rangeLength bottomCount)⟩
  | inr swappedReads =>
      obtain ⟨movedTarget, movedPrefixAtoms, witness, movedDomPin, movedCodPin, seatedSeed,
        _⟩ :=
        arcPairSeated_bubblesThroughPrefix toucherAtom hasCapDomArity hasCapCodArity
          suffixAtoms (windowPosition + 1) windowPosition prefixAtoms
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowFits windowBelowBottom chainedAtSeed
          ⟨swappedReads.1, swappedReads.2, seatBound⟩
      have seatWindowBound : movedTarget.leftContext.length + 2
          ≤ (List.range bottomCount).length := seatedSeed.2.2
      rw [rangeLength bottomCount] at seatWindowBound
      have seatBelowBottom : movedTarget.leftContext.length < bottomCount :=
        Nat.lt_of_lt_of_le
          (Nat.lt_trans (Nat.lt_succ_self movedTarget.leftContext.length)
            (Nat.lt_succ_self (movedTarget.leftContext.length + 1)))
          seatWindowBound
      have firstSeatRead : movedTarget.leftContext.length = windowPosition + 1 :=
        (rangeGetAt_below bottomCount movedTarget.leftContext.length
          seatBelowBottom).symm.trans seatedSeed.1
      have secondSeatRead : movedTarget.leftContext.length + 1 = windowPosition :=
        (rangeGetAt_below bottomCount (movedTarget.leftContext.length + 1)
          seatWindowBound).symm.trans seatedSeed.2.1
      have wouldWrap : windowPosition + 2 = windowPosition :=
        ((congrArg (fun seatValue => seatValue + 1) firstSeatRead).symm.trans
          secondSeatRead)
      exact absurd wouldWrap.symm
        (natNeOfLt (Nat.lt_trans (Nat.lt_succ_self windowPosition)
          (Nat.lt_succ_self (windowPosition + 1))))

/-! ## Honesty marker -/

/-- **Honesty marker — the seed read-off is SHIPPED.**  The `ArcPairCapWindow` certificate
over a boundary-chained spine produces, at the canonical seed, the split plus a bubble
witness whose moved atom is a cap firing at exactly the pinned window position on exactly
the seed boundary; the swapped-order branch is refuted by the seed's range reads.  NOT yet
shipped: identifying the moved atom with the reference head atom
(`adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths`) and assembling the cap-case
discharge of SpineArcHeadExtractionChained.  `= true`. -/
def fxMode_hasArcCapWindowSeedReadoff : Bool := true

end FX1Poly.Polygraph
