import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcNonCrossingFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.NonCrossingShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingIndexBridge

/-! # ArcAdjacentMatchedPair — the extracted matching has an adjacent matched pair (D3 seed)

The short-chord planar lemma `nonCrossing_hasAdjacentMatchedPair` needs THREE applicability hypotheses on the
`partner` matching — all now shipped for the real `extractArc`/`partnerIndexOf` matching via the three fold
capstones:

  * `partnerInRange` — `partnerIndexOf_below` (census-free).
  * `isInvolution` — `partnerIndexOf_isInvolution` (from `ArcBoundaryCensus`, threaded to no-fixed-point).
  * `noFixedPoint` — `partnerIndexOf_neSelf_ofPerfectMatching` (from `ArcPerfectMatchingTokens`).

Together with `IsNonCrossing` (`isNonCrossing_extractArc_diagram_partner`, from `ArcNonCrossing`), the short-chord
lemma FIRES: the extracted matching has a boundary index whose partner sits at the cyclically-adjacent position
— the innermost cup on the boundary.  This is the planar existence fact the D3 spine-readback consumes.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private map/range plumbing (per-file copy) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]; exact Nat.add_zero count

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

/-! ## The adjacent matched pair from the fold invariants -/

/-- ★ **The extracted matching has an adjacent matched pair.**  Given the three fold invariants
(`ArcNonCrossing`, `ArcBoundaryCensus`, `ArcPerfectMatchingTokens`) at a nonempty-boundary state, the
`extractArc` matching's `partner` list is a non-crossing fixed-point-free involution in range, so the
short-chord planar lemma yields a boundary index whose partner sits one cyclic position ahead. -/
theorem hasAdjacentMatchedPair_ofInvariants (bottomCount : Nat) (state : ArcWireState)
    (nonCrossing : ArcNonCrossing bottomCount state)
    (census : ArcBoundaryCensus bottomCount state)
    (perfect : ArcPerfectMatchingTokens bottomCount state)
    (nonEmpty : 0 < bottomCount + state.openWires.length) :
    ∃ shortIndex, shortIndex < (extractArc bottomCount state).diagram.partner.length ∧
      boundaryPosition bottomCount (extractArc bottomCount state).diagram.partner.length shortIndex + 1
        = boundaryPosition bottomCount (extractArc bottomCount state).diagram.partner.length
            (natListGetAt (extractArc bottomCount state).diagram.partner shortIndex) := by
  have partnerLength : (extractArc bottomCount state).diagram.partner.length
      = bottomCount + state.openWires.length := by
    show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
    rw [natListMapLength, rangeLength]
  have partnerRead : ∀ probeIndex, probeIndex < bottomCount + state.openWires.length →
      natListGetAt (extractArc bottomCount state).diagram.partner probeIndex
        = partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
            (bottomCount + state.openWires.length) probeIndex := by
    intro probeIndex probeBelow
    show natListGetAt ((List.range (bottomCount + state.openWires.length)).map
        (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
          (bottomCount + state.openWires.length))) probeIndex = _
    exact natListGetAt_map_range _ (bottomCount + state.openWires.length) probeIndex probeBelow
  have rangePerfect : ArcPerfectMatching bottomCount state :=
    arcPerfectMatching_ofTokens bottomCount state perfect
  have isInvolution : ∀ probeIndex,
      probeIndex < (extractArc bottomCount state).diagram.partner.length →
      natListGetAt (extractArc bottomCount state).diagram.partner
          (natListGetAt (extractArc bottomCount state).diagram.partner probeIndex) = probeIndex := by
    intro probeIndex probeBelow
    rw [partnerLength] at probeBelow
    have notFixed := partnerIndexOf_neSelf_ofPerfectMatching bottomCount state rangePerfect
      probeIndex probeBelow
    have partnerBelow := partnerIndexOf_below state bottomCount probeIndex probeBelow
    rw [partnerRead probeIndex probeBelow,
      partnerRead (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length) probeIndex) partnerBelow]
    exact partnerIndexOf_isInvolution bottomCount state census probeIndex probeBelow notFixed
  have noFixedPoint : ∀ probeIndex,
      probeIndex < (extractArc bottomCount state).diagram.partner.length →
      natListGetAt (extractArc bottomCount state).diagram.partner probeIndex ≠ probeIndex := by
    intro probeIndex probeBelow
    rw [partnerLength] at probeBelow
    rw [partnerRead probeIndex probeBelow]
    exact partnerIndexOf_neSelf_ofPerfectMatching bottomCount state rangePerfect probeIndex probeBelow
  have partnerInRange : ∀ probeIndex,
      probeIndex < (extractArc bottomCount state).diagram.partner.length →
      natListGetAt (extractArc bottomCount state).diagram.partner probeIndex
        < (extractArc bottomCount state).diagram.partner.length := by
    intro probeIndex probeBelow
    rw [partnerLength] at probeBelow ⊢
    rw [partnerRead probeIndex probeBelow]
    exact partnerIndexOf_below state bottomCount probeIndex probeBelow
  exact nonCrossing_hasAdjacentMatchedPair bottomCount (extractArc bottomCount state).diagram.partner
    isInvolution noFixedPoint partnerInRange
    (isNonCrossing_extractArc_diagram_partner bottomCount state nonCrossing)
    (by rw [partnerLength]; exact nonEmpty)

/-! ## The adjacent matched pair at the chained-spine extracted state -/

/-- ★ **The extracted matching of any chained adjunction spine has an adjacent matched pair.**  Folding a
boundary-chained walking-adjunction spine from the canonical seed lands a state whose `extractArc` matching
has a boundary index whose partner is at the cyclically-adjacent position — the boundary's innermost cup,
the D3 spine-readback seed. -/
theorem hasAdjacentMatchedPair_ofChainedSpine
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms)
    (nonEmpty : 0 < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length) :
    ∃ shortIndex,
      shortIndex < (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)).diagram.partner.length ∧
      boundaryPosition bottomCount
          (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)).diagram.partner.length
          shortIndex + 1
        = boundaryPosition bottomCount
          (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)).diagram.partner.length
          (natListGetAt
            (extractArc bottomCount
              (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)).diagram.partner
            shortIndex) :=
  hasAdjacentMatchedPair_ofInvariants bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)
    (arcNonCrossing_ofChainedSpineList bottomCount atoms chained)
    (arcBoundaryCensus_ofChainedSpineList bottomCount atoms chained)
    (arcPerfectMatchingTokens_ofChainedSpineList bottomCount atoms chained)
    nonEmpty

/-! ## Honesty marker -/

/-- **Honesty marker — the short-chord planar lemma FIRES on the real matching (D3 seed).**
`hasAdjacentMatchedPair_ofInvariants` (the three fold invariants → an adjacent matched pair in the extracted
matching) and `hasAdjacentMatchedPair_ofChainedSpine` (its specialisation to any chained adjunction spine's
extracted state).  This is the complete D2 planar foundation delivering the innermost-cup boundary fact.
What this marker does NOT claim: the D3 spine-readback that turns this adjacent-matched boundary pair into a
cup ATOM in the second spine satisfying `windowPin` + `tailsCancel` (the `ArcCupOrbitWitness`).  `= true`. -/
def fxMode_hasArcAdjacentMatchedPair : Bool := true

end FX1Poly.Polygraph
