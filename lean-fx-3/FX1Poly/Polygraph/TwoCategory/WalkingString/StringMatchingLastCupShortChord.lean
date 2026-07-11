import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroProcessSpineTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSortComplete

/-! # WalkingString/StringMatchingLastCupShortChord — the width-0 LOCATE readoff at the adjoint-triple
seed (FC-3 r16, PORT 1)

The walking adjunction's `matchingLastCup_isShortChord` (`MatchingLastCupShortChord`) reads the last cup
of a boundary-chained pure-cup spine off `matchingOfSpineList 0`'s partner list: index
`w = lastCup.leftContext.length` is matched to `w + 1`.  The width-0 pure-cup determinacy consumer the
string valley split needs (`StringWidthZeroPureCupDeterminacyShared`, `StringValleyDegenerateSplit`)
reads the matching at `bottomCount = 0`, so it needs the same readoff at the adjoint-triple seed.

The whole union-find matching engine the readoff rides is `WireState`-only — signature-independent — so it
is REUSED byte-for-byte: `stepCupMatching_forwardPartner` (the general-state cup forward-partner census,
positivity-free) and `wireStateFresh_processSpine_ofAllCup` (the cup-only freshness fold) are imported
verbatim from the adjunction file, no clone.  The port swaps exactly two tokens off the assembly:

  * the cap-tally last-cup-arity read `singletonCupArity` / `capAtomCount_ofAllCupArity`
    (walking-adjunction classifier `adjunctionSpineAtom_isCupOrCap`) → the signature-generic direct
    `AllCupArity`-inversions `allCupArity_lastCup_arity` (`ArcPureCupTransfer`) and
    `allCupArity_prefix_ofAppend` (`ArcCupSortComplete`);
  * the open-wire boundary tracking `processSpine_prefix_openWires_eq_lastDomBoundary` → the shipped
    adjoint-triple `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`
    (`StringWidthZeroProcessSpineTracking`, r15).

Colour-blind throughout: the readoff reads only cup arities + boundary lengths, never `F`/`G`/`H`.

Raw Lean 4 + Init; the private `List.range` read-off plumbing is a per-file copy (the codebase pattern).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private `List.range` read-off plumbing (per-file copies, following the codebase pattern) -/

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

private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below => natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

private theorem natListGetAt_map_range (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  have inRangeList : index < (List.range total).length := by rw [rangeLength]; exact inRange
  rw [natListGetAt_map_below mapFunction (List.range total) index inRangeList,
    rangeGetAt_below total index inRange]

/-! ## The assembly: the last cup reads off as a short chord on the width-0 matching (adjoint-triple seed) -/

/-- ★ **The last cup of a pure-cup string spine reads off as a short chord on the width-`0` matching
(adjoint-triple seed, positivity-free).**  The last atom of a boundary-chained pure-cup spine over the
width-`0` bottom boundary fires LAST, so nothing has split its two legs when it fires: its window
`w = lastCup.leftContext.length` is still adjacent.  In `matchingOfSpineList 0`'s partner list, index `w`
is then matched to `w + 1` — the innermost cup on the boundary.

The three-generator analogue of `matchingLastCup_isShortChord`, swapping the cap-tally arity read for the
generic `allCupArity_lastCup_arity` / `allCupArity_prefix_ofAppend` and the boundary tracking for the
shipped `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`, and REUSING the `WireState`-only
`stepCupMatching_forwardPartner` / `wireStateFresh_processSpine_ofAllCup` engine verbatim.  Colour-blind;
NO `arcDiagram_eq_matching` bridge and NO `0 < bottomCount`. -/
theorem stringMatchingLastCup_isShortChord
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    natListGetAt (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner
        lastCup.leftContext.length
      = lastCup.leftContext.length + 1 := by
  -- the last atom's cup arity, read directly off the pure-cup witness (no cap tally)
  obtain ⟨lastDom, lastCod⟩ := allCupArity_lastCup_arity prefixAtoms lastCup pureCup
  -- the prefix run's invariants (freshness with no sentinel, forest)
  have prefixPure : AllCupArity prefixAtoms := allCupArity_prefix_ofAppend prefixAtoms [lastCup] pureCup
  have freshS : WireStateFresh (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) :=
    wireStateFresh_processSpine_ofAllCup prefixAtoms prefixPure ⟨List.range 0, [], 0, 0⟩
      (wireStateFresh_initial 0)
  have forestS : isUnionFindForest (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).links :=
    isUnionFindForest_processSpine prefixAtoms ⟨List.range 0, [], 0, 0⟩ isUnionFindForest_nil
  have domLen := stringProcessSpine_prefix_openWires_eq_lastDomBoundary 0 prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  -- the forward partner at the prefix state
  have partnerEq := stepCupMatching_forwardPartner
    (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length forestS freshS
    windowFitsS
  -- fold the last cup onto the prefix state and reduce the boundary read
  have structEq : matchingOfSpineList 0 (prefixAtoms ++ [lastCup])
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length) := by
    show extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ (prefixAtoms ++ [lastCup]))
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
    rw [processSpine_append prefixAtoms [lastCup] ⟨List.range 0, [], 0, 0⟩]
    show extractDiagram 0 (stepAtom (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup)
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
    rw [stepAtom_ofCupArity (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup lastDom lastCod]
  rw [structEq]
  -- read the partner list at the window index via the `map`-of-range read-off
  have hStepLen : (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
        lastCup.leftContext.length).openWires.length
      = (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length + 2 :=
    natListInsertAt_length (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires
      lastCup.leftContext.length
      [(processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).nextFresh,
        (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).nextFresh + 1]
  have windowLtTotal : lastCup.leftContext.length
      < (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
          lastCup.leftContext.length).openWires.length := by
    rw [hStepLen]
    exact Nat.lt_of_le_of_lt windowFitsS
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _))
  have partnerListEq : (extractDiagram 0
        (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)).partner
      = (List.range (0 + (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
            lastCup.leftContext.length).openWires.length)).map
          (partnerIndexOf (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
              lastCup.leftContext.length).links
            (List.range 0 ++ (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
                lastCup.leftContext.length).openWires)
            (0 + (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
                lastCup.leftContext.length).openWires.length)) := rfl
  rw [partnerListEq]
  rw [natListGetAt_map_range _
    (0 + (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
        lastCup.leftContext.length).openWires.length)
    lastCup.leftContext.length (by rw [Nat.zero_add]; exact windowLtTotal)]
  -- collapse `0 + · = ·` (`List.range 0 ++ · = ·` is definitional), then apply the forward partner
  rw [Nat.zero_add]
  exact partnerEq

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-`0` LOCATE readoff is ported to the adjoint-triple seed (FC-3 r16, PORT
1).**  `stringMatchingLastCup_isShortChord` reads the last cup of a boundary-chained pure-cup string spine
off `matchingOfSpineList 0`'s partner list as the short chord `w ↦ w + 1`, the adjoint-triple analogue of
`matchingLastCup_isShortChord`.  Two token swaps (the generic `allCupArity_lastCup_arity` /
`allCupArity_prefix_ofAppend` arity reads + the shipped `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`
tracking) over the byte-for-byte-REUSED `WireState`-only `stepCupMatching_forwardPartner` /
`wireStateFresh_processSpine_ofAllCup` engine.  Colour-blind; positivity-free.

  What this marker does NOT close (no gate flag flips): the width-0 pure-cup SORT inhabiting
  `StringWidthZeroPureCupDeterminacyShared`.  On top of this readoff the sort still needs the chord-shift
  descents (PORT 2), the drop-injectivity (PORT 3), and the word-threaded locate/sort assembly.  So
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false`, honestly.
  `= true`. -/
def fxString_hasMatchingLastCupShortChord : Bool := true

end FX1Poly.Polygraph
