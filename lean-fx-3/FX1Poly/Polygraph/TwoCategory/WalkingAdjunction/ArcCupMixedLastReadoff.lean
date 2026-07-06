import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff

/-! # ArcCupMixedLastReadoff — the last cup of a MIXED spine reads off as a short chord (S1-mixed)

`pureCupSpine_lastCup_isShortChord` (`ArcCupLastCupReadoff`) reads the last cup of a boundary-chained
PURE-cup spine off the boundary matching as an adjacent short chord.  Its `AllCupArity` premise on the
WHOLE spine is only ever consumed to prove one fact: the LAST atom is a cup (`generatorDom.length = 0`,
`generatorCod.length = 2`).  Every OTHER ingredient is already general over a mixed (cup AND cap) prefix:

  * the incoming-state invariants — `arcStateFresh_processArcSpine`, `isUnionFindForest_processArcSpine`,
    `arcBoundaryCensus_ofChainedSpineList` — fold over `stepArcAtom`, which dispatches cup/cap per atom
    via `adjunctionSpineAtom_hasCupOrCapArity`, so they hold for ANY boundary-chained adjunction prefix;
  * the open-wire tracker `processArcSpine_prefix_openWires_eq_lastDomBoundary` reads only lengths and is
    already mixed-general;
  * `generalStateCupForwardPartner` reads the last cup's two fresh legs off an ARBITRARY invariant-carrying
    incoming state (it never inspects the prefix's arities).

So the generalization is mechanical: drop `AllCupArity` on the whole spine, keep only that the LAST atom
is a cup.  This is the mixed-spine S1 foundation for the peel-LAST route (D) to the walking-adjunction
cell reconstruction — the last cup's boundary chord is arc-readable regardless of what the tail composed
below it.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / map plumbing (per-file copy — the sibling kits are file-private) -/

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

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]; exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

private theorem natListMapLength (mapFunction : Nat → Nat) :
    (list : List Nat) → (list.map mapFunction).length = list.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (natListMapLength mapFunction rest)

private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below =>
      natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

private theorem natListGetAt_map_range (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  have inRangeList : index < (List.range total).length := by rw [rangeLength]; exact inRange
  rw [natListGetAt_map_below mapFunction (List.range total) index inRangeList,
    rangeGetAt_below total index inRange]

/-! ## S1-mixed — the last cup of a mixed spine reads off as a short chord -/

/-- ★ **The last cup of a MIXED spine reads off as a short chord (raw-index adjacent matched pair).**
The generalization of `pureCupSpine_lastCup_isShortChord` dropping the whole-spine `AllCupArity`: the
prefix `prefixAtoms` may compose ANY mix of cups and caps, as long as the boundary chain holds and the
LAST atom is a cup (`lastDom : generatorDom.length = 0`, `lastCod : generatorCod.length = 2`).  The last
cup fires LAST, so nothing splits its two legs — its window `w = lastCup.leftContext.length` is still
adjacent when it fires — and in the extracted arc structure's boundary matching the raw top-port index
`bottomCount + w` reads its partner `bottomCount + w + 1`.

The tail's composition only affects the INCOMING state, which `generalStateCupForwardPartner` handles from
any state carrying the shipped invariants; those invariants (fresh / forest / census / seed-bound) fold
over the mixed prefix via `stepArcAtom`'s cup/cap dispatch.  This is the peel-LAST (route D) S1 foundation:
the last cup's boundary chord is arc-readable regardless of the mixed tail below it. -/
theorem mixedSpine_lastCup_isShortChord
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]))
    (lastDom : lastCup.generatorDom.length = 0)
    (lastCod : lastCup.generatorCod.length = 2) :
    natListGetAt (arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner
        (bottomCount + lastCup.leftContext.length)
      = bottomCount + lastCup.leftContext.length + 1 := by
  -- the prefix run's shipped invariants (all mixed-general: they fold cup/cap via stepArcAtom)
  have prefixChained : SpineBoundaryChained bottomCount prefixAtoms :=
    spineBoundaryChained_prefix_ofAppend prefixAtoms [lastCup] bottomCount chained
  have freshS := arcStateFresh_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) (arcStateFresh_initial bottomCount)
  have forestS := isUnionFindForest_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) isUnionFindForest_nil
  have censusS := arcBoundaryCensus_ofChainedSpineList bottomCount prefixAtoms prefixChained
  have seedBelowS := seedBottomCount_le_processArcSpine_nextFresh bottomCount prefixAtoms
  have domLen := processArcSpine_prefix_openWires_eq_lastDomBoundary bottomCount prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans
      (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  -- the general-state cup forward partner at the prefix state
  have partnerEq := generalStateCupForwardPartner bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
    lastCup.leftContext.length forestS freshS seedBelowS censusS windowFitsS
  -- fold the last cup onto the prefix state and reduce the boundary read
  have structEq : arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length) := by
    show extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          (prefixAtoms ++ [lastCup]))
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)
    rw [processArcSpine_append prefixAtoms [lastCup]
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])]
    show extractArc bottomCount
        (stepArcAtom (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms) lastCup)
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)
    rw [stepArcAtom_eq_stepCupArc
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
      lastCup lastDom lastCod]
  rw [structEq]
  have hStepLen :
      (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms) lastCup.leftContext.length).openWires.length
        = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms).openWires.length + 2 :=
    natListInsertAt_length
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms).openWires
      lastCup.leftContext.length
      [(processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms).nextFresh,
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).nextFresh + 1]
  have rangeBound : bottomCount + lastCup.leftContext.length
      < bottomCount
        + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length).openWires.length := by
    rw [hStepLen]
    exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt windowFitsS
        (Nat.lt_of_lt_of_le
          (Nat.lt_succ_self
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires.length)
          (Nat.le_succ
            ((processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires.length + 1))))
      bottomCount
  have partnerListEq :
      (extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)).diagram.partner
        = (List.range (bottomCount
            + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                prefixAtoms) lastCup.leftContext.length).openWires.length)).map
            (partnerIndexOf
              (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                prefixAtoms) lastCup.leftContext.length).links
              (List.range bottomCount
                ++ (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    prefixAtoms) lastCup.leftContext.length).openWires)
              (bottomCount
                + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    prefixAtoms) lastCup.leftContext.length).openWires.length)) := rfl
  rw [partnerListEq, natListGetAt_map_range _
    (bottomCount
      + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms) lastCup.leftContext.length).openWires.length)
    (bottomCount + lastCup.leftContext.length) rangeBound]
  exact partnerEq

end FX1Poly.Polygraph
