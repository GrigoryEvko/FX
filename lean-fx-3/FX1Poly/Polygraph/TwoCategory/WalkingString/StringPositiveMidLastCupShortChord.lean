import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingStepCupWindowPartner

/-! # WalkingString/StringPositiveMidLastCupShortChord — the LOCATE readoff at a POSITIVE mid-width bottom
boundary (FC-3 r44, P2b: the positive-mid short-chord)

The width-`0` LOCATE readoff `stringMatchingLastCup_isShortChord` (r16, `StringMatchingLastCupShortChord`)
reads the last cup of a boundary-chained pure-cup spine off `matchingOfSpineList 0`'s partner list: window
`w = lastCup.leftContext.length` matches `w + 1`.  The positive-mid pure-cup determinacy brick
`StringPositiveMidPureCupDeterminacy` (`StringPositiveMidCupSortResidual`, r40) needs the SAME readoff at an
arbitrary bottom boundary `midWidth` — the survivor through-strands the cup legs interleave with.

This file ships that generalization as a PARAMETERIZED SIBLING of the r16 readoff — it does NOT edit the
shipped width-`0` file.  The proof is the r16 proof with exactly three offset edits (seed `List.range 0 →
List.range midWidth` / `wireStateFresh_initial 0 → midWidth`; the seed-`0`-specialized forward partner
`stepCupMatching_forwardPartner` → the SHIPPED seed-general `generalStateCupForwardPartnerMatching midWidth`
(`MatchingStepCupWindowPartner`); and dropping the `0 + · = ·` / `List.range 0 ++ · = ·` definitional
collapses, so the read lands at the genuine offset index `midWidth + w`).  The one new obligation the seed-
general partner opens is the `seedBoundary ≤ nextFresh` premise, discharged in one line by the shipped
counter monotonicity `processSpine_nextFresh_le` (the seed's `nextFresh` is `midWidth`, and the fold never
lowers it).

**Positivity-free** (RECON finding): the readoff needs NO `0 < midWidth`.  It rides the `WireState` engine
directly (NOT the arc bridge `arcDiagram_eq_matching`, which would burn a `0 < bottomCount`), so the general
statement SUBSUMES the r16 width-`0` readoff as its `midWidth := 0` case.  The `0 < midWidth` the doubly-
positive wall consumes enters later, at the snake exclusion (`stringMatchingForwardChordsNotAdjacent_mid`,
r43 P2a), not here.  Colour-blind throughout: reads only cup arities + boundary lengths, never `F`/`G`/`H`.

Raw Lean 4 + Init; the private `List.range` read-off plumbing is a per-file copy (the codebase pattern, the
r16/r38/r42/r43 anti-`List.length_range`-propext discipline).  `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin, `#print axioms`
in the independent witness. -/

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

/-! ## The assembly: the last cup reads off as a short chord on the `matchingOfSpineList midWidth` matching -/

/-- ★ **The last cup of a pure-cup string spine reads off as a short chord on the `matchingOfSpineList
midWidth` matching (positive-mid, positivity-free).**  The last atom of a boundary-chained pure-cup spine
over an arbitrary bottom boundary `midWidth` fires LAST, so nothing has split its two legs when it fires:
its window `w = lastCup.leftContext.length` is still adjacent.  In `matchingOfSpineList midWidth`'s partner
list the OFFSET index `midWidth + w` — `w` above the `midWidth` through-strand survivors — is then matched
to `midWidth + w + 1`, the innermost cup on the boundary.

The positive-mid generalization of the r16 `stringMatchingLastCup_isShortChord`: the SAME `WireState`-only
engine (`wireStateFresh_processSpine_ofAllCup` / `isUnionFindForest_processSpine`), swapping the seed-`0`
forward partner `stepCupMatching_forwardPartner` for the SHIPPED seed-general
`generalStateCupForwardPartnerMatching midWidth` (`MatchingStepCupWindowPartner`) and seeding the fold from
`⟨List.range midWidth, [], midWidth, 0⟩`.  The one new obligation — `midWidth ≤ nextFresh` — is one line off
the shipped counter monotonicity `processSpine_nextFresh_le`.  NO `arcDiagram_eq_matching` bridge, NO
`0 < midWidth`: SUBSUMES the r16 width-`0` readoff at `midWidth := 0`. -/
theorem stringMatchingLastCup_isShortChord_mid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    natListGetAt (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner
        (midWidth + lastCup.leftContext.length)
      = midWidth + lastCup.leftContext.length + 1 := by
  -- the last atom's cup arity, read directly off the pure-cup witness (no cap tally)
  obtain ⟨lastDom, lastCod⟩ := allCupArity_lastCup_arity prefixAtoms lastCup pureCup
  -- the prefix run's invariants (freshness with no sentinel, forest) — seeded at width `midWidth`
  have prefixPure : AllCupArity prefixAtoms := allCupArity_prefix_ofAppend prefixAtoms [lastCup] pureCup
  have freshS : WireStateFresh (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) :=
    wireStateFresh_processSpine_ofAllCup prefixAtoms prefixPure ⟨List.range midWidth, [], midWidth, 0⟩
      (wireStateFresh_initial midWidth)
  have forestS : isUnionFindForest (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).links :=
    isUnionFindForest_processSpine prefixAtoms ⟨List.range midWidth, [], midWidth, 0⟩ isUnionFindForest_nil
  -- NEW vs r16: the seed-below-fresh witness the seed-general partner needs (the seed's `nextFresh` is
  -- `midWidth`, and the fold never lowers it).
  have seedBelowS : midWidth
      ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh :=
    processSpine_nextFresh_le prefixAtoms ⟨List.range midWidth, [], midWidth, 0⟩
  have domLen := stringProcessSpine_prefix_openWires_eq_lastDomBoundary midWidth prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  -- the SEED-GENERAL forward partner at the prefix state (offset by `midWidth`)
  have partnerEq := generalStateCupForwardPartnerMatching midWidth
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup.leftContext.length
    forestS freshS seedBelowS windowFitsS
  -- fold the last cup onto the prefix state and reduce the boundary read
  have structEq : matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])
      = extractDiagram midWidth
          (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
            lastCup.leftContext.length) := by
    show extractDiagram midWidth
        (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ (prefixAtoms ++ [lastCup]))
      = extractDiagram midWidth
          (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
            lastCup.leftContext.length)
    rw [processSpine_append prefixAtoms [lastCup] ⟨List.range midWidth, [], midWidth, 0⟩]
    show extractDiagram midWidth
        (stepAtom (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup)
      = extractDiagram midWidth
          (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
            lastCup.leftContext.length)
    rw [stepAtom_ofCupArity (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup
      lastDom lastCod]
  rw [structEq]
  -- read the partner list at the OFFSET window index via the `map`-of-range read-off
  have hStepLen : (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
        lastCup.leftContext.length).openWires.length
      = (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2 :=
    natListInsertAt_length (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires
      lastCup.leftContext.length
      [(processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh,
        (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh + 1]
  have windowLtTotal : lastCup.leftContext.length
      < (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
          lastCup.leftContext.length).openWires.length := by
    rw [hStepLen]
    exact Nat.lt_of_le_of_lt windowFitsS
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _))
  have partnerListEq : (extractDiagram midWidth
        (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
          lastCup.leftContext.length)).partner
      = (List.range (midWidth + (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
            lastCup.leftContext.length).openWires.length)).map
          (partnerIndexOf (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
              lastCup.leftContext.length).links
            (List.range midWidth ++ (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
                lastCup.leftContext.length).openWires)
            (midWidth + (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
                lastCup.leftContext.length).openWires.length)) := rfl
  rw [partnerListEq]
  rw [natListGetAt_map_range _
    (midWidth + (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
        lastCup.leftContext.length).openWires.length)
    (midWidth + lastCup.leftContext.length)
    (Nat.add_lt_add_left windowLtTotal midWidth)]
  -- the read lands at the genuine OFFSET index `midWidth + w`; no `0 + · = ·` collapse to apply
  exact partnerEq

/-! ## The fixtures: real pure-cup last-cup spines at POSITIVE mid-width (mid-1 AND mid-2)

Both fixtures are single upper cups `η' = StringTwoCell.unitUpper` (`id_tip ⇒ G·H`, arity `(0, 2)`) at
window `0`, riding a genuine survivor context so the bottom boundary is positive.  The mid-`1` fixture rides
a single survivor strand `G` (rightContext `= G`, `domBoundaryLength = 1`); the mid-`2` fixture rides two
survivor strands `G·H` (rightContext `= G·H`, `domBoundaryLength = 2`). -/

/-- The single survivor strand `G : tip ⟶ base` (`domBoundaryLength = 1` context). -/
def stringSurvivorG : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base :=
  ModalityPath.cons AdjointTripleModality.right
    (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)

/-- Cup `η'` at window `0` over a SINGLE survivor strand `G` (leftContext `id_tip`, rightContext `G`) — a
genuine mid-`1` pure-cup last cup (`domBoundaryLength = 1`). -/
def stringMidOneCupOverG :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.base :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper, stringSurvivorG⟩

/-- Cup `η'` at window `0` over TWO survivor strands `G·H` (leftContext `id_tip`, rightContext `G·H`) — a
genuine mid-`2` pure-cup last cup (`domBoundaryLength = 2`). -/
def stringMidTwoCupOverGH :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    stringGH, StringTwoCell.unitUpper, stringGH⟩

/-! ### Concrete-matching certificates — the genuinely-COMPUTED partner lists (anti-vacuity) -/

/-- The mid-`1` boundary matching computes to the concrete partner list `[3, 2, 1, 0]`: the single survivor
`0` links top-to-bottom (index `0 ↔ 3`), and the cup's two fresh legs sit at boundary indices `1, 2` ABOVE
the survivor (`1 ↔ 2`).  So `partner[1] = 2` is a genuinely-computed value, not a vacuous coincidence. -/
theorem stringMidOneCupOverG_matchingComputes :
    (matchingOfSpineList 1 [stringMidOneCupOverG]).partner = [3, 2, 1, 0] := by decide

/-- The mid-`2` boundary matching computes to the concrete partner list `[4, 5, 3, 2, 0, 1]`: the two
survivors `0, 1` link top-to-bottom (indices `0 ↔ 4`, `1 ↔ 5`), and the cup's two fresh legs sit at boundary
indices `2, 3` ABOVE the two survivors (`2 ↔ 3`).  So `partner[2] = 3` is a genuinely-computed value. -/
theorem stringMidTwoCupOverGH_matchingComputes :
    (matchingOfSpineList 2 [stringMidTwoCupOverGH]).partner = [4, 5, 3, 2, 0, 1] := by decide

/-! ### The fires — `stringMatchingLastCup_isShortChord_mid` on the two positive-mid fixtures -/

/-- ★ **P2b FIRES at mid-`1`.**  `stringMatchingLastCup_isShortChord_mid` at `midWidth = 1` on the single-
survivor cup reads its window `0` off `matchingOfSpineList 1`'s partner list at the OFFSET index
`1 + 0 = 1`, matching `1 + 0 + 1 = 2` — agreeing with the genuinely-computed `partner[1] = 2`
(`stringMidOneCupOverG_matchingComputes`).  Every chaining / arity hypothesis is `rfl` (`domBoundaryLength =
1`, `generatorDom.length = 0`, `generatorCod.length = 2`). -/
theorem stringMatchingLastCupShortChord_mid_firesAtMidOne :
    natListGetAt (matchingOfSpineList 1 [stringMidOneCupOverG]).partner 1 = 2 :=
  stringMatchingLastCup_isShortChord_mid 1 [] stringMidOneCupOverG
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))
    (AllCupArity.cons rfl rfl AllCupArity.nil)

/-- ★ **P2b FIRES at mid-`2`.**  `stringMatchingLastCup_isShortChord_mid` at `midWidth = 2` on the two-
survivor cup reads its window `0` off `matchingOfSpineList 2`'s partner list at the OFFSET index
`2 + 0 = 2`, matching `2 + 0 + 1 = 3` — agreeing with the genuinely-computed `partner[2] = 3`
(`stringMidTwoCupOverGH_matchingComputes`).  The offset is genuinely `midWidth = 2` above the survivors:
this is the survivor-through-strand re-ranking the width-`0` readoff never exercises. -/
theorem stringMatchingLastCupShortChord_mid_firesAtMidTwo :
    natListGetAt (matchingOfSpineList 2 [stringMidTwoCupOverGH]).partner 2 = 3 :=
  stringMatchingLastCup_isShortChord_mid 2 [] stringMidTwoCupOverGH
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))
    (AllCupArity.cons rfl rfl AllCupArity.nil)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the LOCATE last-cup readoff is generalized to a POSITIVE mid-width bottom boundary
(FC-3 r44, P2b).**  `stringMatchingLastCup_isShortChord_mid` reads the last cup of a boundary-chained pure-
cup string spine off `matchingOfSpineList midWidth`'s partner list as the OFFSET short chord `midWidth + w ↦
midWidth + w + 1`, the positive-mid generalization of the r16 `stringMatchingLastCup_isShortChord`.  Three
offset edits over the byte-for-byte-REUSED `WireState` engine (seed `List.range midWidth`; the SHIPPED seed-
general `generalStateCupForwardPartnerMatching midWidth` with its `midWidth ≤ nextFresh` premise off
`processSpine_nextFresh_le`; dropping the `0 + · = ·` collapses).  Colour-blind; positivity-FREE, so it
SUBSUMES the r16 width-`0` readoff.  FIRED at mid-`1` AND mid-`2` on genuine single- and double-survivor
cup fixtures, each cross-checked against the genuinely-COMPUTED partner list (`[3,2,1,0]` / `[4,5,3,2,0,1]`).

  CENSUS (N/K): P2b delivers K = 1 named width-generic readoff brick, PROVED (N_proved = 1) + 2 concrete
  fires + 2 concrete-matching certificates.  0 sub-Props inhabited, 0 masters flipped.

  What this does NOT close (no gate flag flips): the positive-mid pure-cup SORT inhabiting the brick
  `StringPositiveMidPureCupDeterminacy` (`StringPositiveMidCupSortResidual`).  On top of this readoff the
  positive-mid LOCATE still needs the chord-shift descents (`stringMatchingChordShift_below/above_mid`, the
  seed-offset ports riding `diagramPartner_stepCup midWidth`), the drop-injectivity
  (`stringDropLastCup_matching_injective_mid`), the empty-mid survivor-identity base floor
  (`stringEmptyMidMatching_isSurvivorIdentity`, the one genuinely-new invariant, the DUAL of the shipped
  `initialPartner_bottomPort_ge`), and the fueled word-threaded locate/sort assembly.  So the brick stays
  OPEN and `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) /
  `fxString_hasConvOfMapEqPortFlip` (`StringConvOfMapEqPort`) STAY `false`, honestly.  `= true`. -/
def fxString_hasPositiveMidLastCupShortChord : Bool := true

end FX1Poly.Polygraph
