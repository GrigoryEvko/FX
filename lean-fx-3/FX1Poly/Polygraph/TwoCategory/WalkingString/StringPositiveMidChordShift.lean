import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDropLastCup

/-! # WalkingString/StringPositiveMidChordShift — the POSITIVE-mid chord-shift twins (FC-3 r45, R1)

The width-`0` chord-shift descents `stringMatchingChordShift_below` / `stringMatchingChordShift_above`
(`StringMatchingWidthZeroChordShift`, r16 PORT 2) read forward chords off `matchingOfSpineList 0`'s partner
list and track how a chord survives dropping the located last cup: below the window unshifted, above the
window shifted down by two (the snake position `wlast + 1` arithmetically impossible).  The positive-mid
pure-cup determinacy brick `StringPositiveMidPureCupDeterminacy` (`StringPositiveMidCupSortResidual`) drives
its LOCATE off `matchingOfSpineList midWidth` (the through-strand survivor count), so it needs the SAME
descents at the arbitrary `midWidth` bottom boundary.  This file ships the two positive-mid siblings.

Both are OFFSET ports (`0 ⤳ midWidth`), NOT genuine re-rankings — the byte-for-byte-REUSED `WireState`-only
partner-splice engine `diagramPartner_stepCup` (whose window partners are the census-free
`generalStateCup{Forward,Backward}PartnerMatching`) is `seedBoundary`-general, so the descents ride it at
`seedBoundary := midWidth`.  Two edits over the r16 chord-shift proof:

  * the seed `⟨List.range 0, [], 0, 0⟩ ⤳ ⟨List.range midWidth, [], midWidth, 0⟩` (so the read lands at the
    genuine offset window index `midWidth + w`, with no `0 + · = ·` collapse to apply);
  * the ONE new obligation the seed-general splice opens — the `seedBoundary ≤ nextFresh` premise
    `midWidth ≤ (processSpine ⟨List.range midWidth, …⟩ prefixAtoms).nextFresh` — discharged in one line by
    the shipped counter monotonicity `processSpine_nextFresh_le` (the seed's `nextFresh` is `midWidth`, and
    the fold never lowers it).  This is the `(Nat.zero_le _)` slot of the width-`0` proof.

Positivity-FREE (RECON finding): the descents read partner indices + windows arithmetically, never the
involution, so they need NO `0 < midWidth`; the general statement SUBSUMES the r16 width-`0` descents at
`midWidth := 0`.  Colour-blind throughout: reads partner indices + windows, never `F`/`G`/`H`.

Raw Lean 4 + Init; the private range / map / Nat plumbing is a per-file copy (the codebase pattern, the
r16/r38/r42/r43/r44 anti-`List.length_range`-propext discipline).  `propext`/`Quot.sound`/`Classical`/
`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin,
`#print axioms` in the independent witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / map / Nat plumbing (per-file copies, following the codebase pattern) -/

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
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

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

private theorem natListGetAt_zeroOfGe :
    (list : List Nat) → (index : Nat) → list.length ≤ index → natListGetAt list index = 0
  | [], _, _ => rfl
  | _ :: _, 0, atLeast => absurd atLeast (Nat.not_succ_le_zero _)
  | _ :: rest, index + 1, atLeast =>
      natListGetAt_zeroOfGe rest index (Nat.le_of_succ_le_succ atLeast)

private theorem natAddRightCancel :
    (added : Nat) → {leftSide rightSide : Nat} →
    leftSide + added = rightSide + added → leftSide = rightSide
  | 0, _, _, sumsEqual => sumsEqual
  | added + 1, _, _, sumsEqual => natAddRightCancel added (Nat.succ.inj sumsEqual)

private theorem natAddSubCancel (baseValue : Nat) : (subtracted : Nat) →
    baseValue + subtracted - subtracted = baseValue
  | 0 => rfl
  | subtracted + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact natAddSubCancel baseValue subtracted

private theorem natSum_middle2 (a b c : Nat) : a + (b + 2 + c) = a + b + c + 2 := by
  rw [Nat.add_right_comm b 2 c, ← Nat.add_assoc a (b + c) 2, ← Nat.add_assoc a b c]

/-- The partner list has length `midWidth + openWires` (per-file copy of the private
`extractDiagram_partner_length`, at the positive-mid seed). -/
private theorem extractDiagram_partner_length_mid (midWidth : Nat) (state : WireState) :
    (extractDiagram midWidth state).partner.length = midWidth + state.openWires.length := by
  show ((List.range (midWidth + state.openWires.length)).map
      (partnerIndexOf state.links (List.range midWidth ++ state.openWires)
        (midWidth + state.openWires.length))).length = midWidth + state.openWires.length
  rw [natListMapLength, rangeLength]

/-! ## The chord-shift setup (rides brick-3 `diagramPartner_stepCup` at the `midWidth` seed) -/

/-- The shared setup for the positive-mid chord-shift readoffs: the last cup folds onto the processed prefix
as a top-of-stack cup, the partner list splices/shifts over the window by the shipped `diagramPartner_stepCup`
at `seedBoundary := midWidth`, the window fits, and the base partner length reflects.  The one new obligation
over the width-`0` setup is the seed-below-fresh witness (`midWidth ≤ nextFresh`) off `processSpine_nextFresh_le`. -/
private theorem stringMatchingChordShiftSetupMid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    ((matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner
        = natListInsertAt
            ((matchingOfSpineList midWidth prefixAtoms).partner.map
              (freshShiftAbove (midWidth + lastCup.leftContext.length) 2))
            (midWidth + lastCup.leftContext.length)
            [midWidth + lastCup.leftContext.length + 1, midWidth + lastCup.leftContext.length])
      ∧ lastCup.leftContext.length
          ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length
      ∧ (matchingOfSpineList midWidth prefixAtoms).partner.length
          = midWidth + (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length := by
  obtain ⟨lastDom, lastCod⟩ := allCupArity_lastCup_arity prefixAtoms lastCup pureCup
  have prefixPure : AllCupArity prefixAtoms := allCupArity_prefix_ofAppend prefixAtoms [lastCup] pureCup
  have freshS : WireStateFresh (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) :=
    wireStateFresh_processSpine_ofAllCup prefixAtoms prefixPure ⟨List.range midWidth, [], midWidth, 0⟩
      (wireStateFresh_initial midWidth)
  have forestS : isUnionFindForest (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).links :=
    isUnionFindForest_processSpine prefixAtoms ⟨List.range midWidth, [], midWidth, 0⟩ isUnionFindForest_nil
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
  refine ⟨?_, windowFitsS, extractDiagram_partner_length_mid _ _⟩
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
  exact diagramPartner_stepCup midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
    lastCup.leftContext.length freshS forestS seedBelowS windowFitsS

/-! ## The chord-shift descents -/

/-- ★ **Chord-shift, below the dropped cup (positive-mid, positivity-free).**  A forward chord
`(targetWindow, +1)` in `matchingOf midWidth (prefix ++ [lastCup])` at a window strictly below the last cup's
window survives the drop UNSHIFTED into `matchingOf midWidth prefix`.  Positive-mid analogue of
`stringMatchingChordShift_below`; OFFSET port `0 ⤳ midWidth`. -/
theorem stringMatchingChordShift_below_mid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup]))
    (targetWindow : Nat)
    (targetBelow : targetWindow < lastCup.leftContext.length)
    (chordAt : natListGetAt
        (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner
        (midWidth + targetWindow)
      = midWidth + targetWindow + 1) :
    natListGetAt (matchingOfSpineList midWidth prefixAtoms).partner
        (midWidth + targetWindow)
      = midWidth + targetWindow + 1 := by
  obtain ⟨partnerSplice, windowFitsS, baseLen⟩ :=
    stringMatchingChordShiftSetupMid midWidth prefixAtoms lastCup chained pureCup
  rw [partnerSplice] at chordAt
  have indexBelowPos : midWidth + targetWindow < midWidth + lastCup.leftContext.length :=
    Nat.add_lt_add_left targetBelow midWidth
  have indexBelowLen : midWidth + targetWindow
      < ((matchingOfSpineList midWidth prefixAtoms).partner.map
          (freshShiftAbove (midWidth + lastCup.leftContext.length) 2)).length := by
    rw [natListMapLength, baseLen]
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le targetBelow windowFitsS) midWidth
  have indexBelowBaseLen : midWidth + targetWindow
      < (matchingOfSpineList midWidth prefixAtoms).partner.length := by
    rw [baseLen]
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le targetBelow windowFitsS) midWidth
  rw [natListGetAt_natListInsertAt_below _ _ _ _ indexBelowPos indexBelowLen,
    natListGetAt_map_below _ _ _ indexBelowBaseLen] at chordAt
  cases Nat.lt_or_ge
      (natListGetAt (matchingOfSpineList midWidth prefixAtoms).partner (midWidth + targetWindow))
      (midWidth + lastCup.leftContext.length) with
  | inl isBelow =>
      rw [freshShiftAbove_ofNotLe _ _ _ (Nat.not_le.mpr isBelow)] at chordAt
      exact chordAt
  | inr isAtOrAbove =>
      exfalso
      rw [freshShiftAbove_ofLe _ _ _ isAtOrAbove] at chordAt
      have chainBound : midWidth + lastCup.leftContext.length + 2 ≤ midWidth + targetWindow + 1 :=
        chordAt ▸ Nat.add_le_add_right isAtOrAbove 2
      have : midWidth + lastCup.leftContext.length ≤ midWidth + targetWindow :=
        Nat.le_of_succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ 1)) chainBound)
      exact Nat.not_lt.mpr this indexBelowPos

/-- ★ **Chord-shift, above the dropped cup (positive-mid, positivity-free).**  A forward chord
`(targetWindow, +1)` in `matchingOf midWidth (prefix ++ [lastCup])` at a window strictly above the last cup's
window survives the drop shifted DOWN BY TWO into `matchingOf midWidth prefix` at `targetWindow - 2`; the
snake position `targetWindow = wlast + 1` is arithmetically impossible.  Positive-mid analogue of
`stringMatchingChordShift_above`; OFFSET port `0 ⤳ midWidth`. -/
theorem stringMatchingChordShift_above_mid
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup]))
    (targetWindow : Nat)
    (targetAbove : lastCup.leftContext.length < targetWindow)
    (chordAt : natListGetAt
        (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner
        (midWidth + targetWindow)
      = midWidth + targetWindow + 1) :
    natListGetAt (matchingOfSpineList midWidth prefixAtoms).partner
        (midWidth + (targetWindow - 2))
      = midWidth + (targetWindow - 2) + 1 := by
  obtain ⟨partnerSplice, windowFitsS, baseLen⟩ :=
    stringMatchingChordShiftSetupMid midWidth prefixAtoms lastCup chained pureCup
  have fullLen : (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner.length
      = (matchingOfSpineList midWidth prefixAtoms).partner.length + 2 := by
    rw [partnerSplice, natListInsertAt_length, natListMapLength]
    rfl
  have targetInFull : midWidth + targetWindow
      < (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner.length := by
    cases Nat.lt_or_ge (midWidth + targetWindow)
        (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner.length with
    | inl inRange => exact inRange
    | inr outRange =>
        exfalso
        rw [natListGetAt_zeroOfGe _ _ outRange] at chordAt
        exact Nat.noConfusion chordAt
  have targetLtTotal : targetWindow
      < (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2 := by
    rw [fullLen, baseLen, Nat.add_assoc] at targetInFull
    exact Nat.lt_of_add_lt_add_left targetInFull
  cases Nat.lt_or_ge targetWindow (lastCup.leftContext.length + 2) with
  | inl targetSnake =>
      have targetIsSnake : targetWindow = lastCup.leftContext.length + 1 :=
        Nat.le_antisymm (Nat.le_of_succ_le_succ targetSnake) targetAbove
      exfalso
      rw [partnerSplice, targetIsSnake] at chordAt
      have snakeRead : natListGetAt
          (natListInsertAt
            ((matchingOfSpineList midWidth prefixAtoms).partner.map
              (freshShiftAbove (midWidth + lastCup.leftContext.length) 2))
            (midWidth + lastCup.leftContext.length)
            [midWidth + lastCup.leftContext.length + 1, midWidth + lastCup.leftContext.length])
          (midWidth + (lastCup.leftContext.length + 1))
        = midWidth + lastCup.leftContext.length := by
        rw [← Nat.add_assoc midWidth lastCup.leftContext.length 1]
        exact natListGetAt_natListInsertAt_inside _ _ _ 1 (Nat.lt_succ_self 1)
          (by rw [natListMapLength, baseLen]; exact Nat.add_le_add_left windowFitsS midWidth)
      rw [snakeRead] at chordAt
      exact absurd chordAt (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _)))
  | inr targetAtLeast =>
      obtain ⟨offset, offsetSpec⟩ := Nat.le.dest targetAtLeast
      subst offsetSpec
      rw [partnerSplice] at chordAt
      have windowReduce : lastCup.leftContext.length + 2 + offset - 2 = lastCup.leftContext.length + offset := by
        rw [Nat.add_right_comm lastCup.leftContext.length 2 offset]
        exact natAddSubCancel (lastCup.leftContext.length + offset) 2
      rw [windowReduce, ← Nat.add_assoc midWidth lastCup.leftContext.length offset]
      have readEq : natListGetAt
            (natListInsertAt
              ((matchingOfSpineList midWidth prefixAtoms).partner.map
                (freshShiftAbove (midWidth + lastCup.leftContext.length) 2))
              (midWidth + lastCup.leftContext.length)
              [midWidth + lastCup.leftContext.length + 1, midWidth + lastCup.leftContext.length])
            (midWidth + (lastCup.leftContext.length + 2 + offset))
          = natListGetAt
              ((matchingOfSpineList midWidth prefixAtoms).partner.map
                (freshShiftAbove (midWidth + lastCup.leftContext.length) 2))
              (midWidth + lastCup.leftContext.length + offset) := by
        rw [natSum_middle2 midWidth lastCup.leftContext.length offset]
        exact natListGetAt_natListInsertAt_pastBlock _ _ _ offset
          (by rw [natListMapLength, baseLen]; exact Nat.add_le_add_left windowFitsS midWidth)
      rw [readEq] at chordAt
      have wPrimeLtBase : midWidth + lastCup.leftContext.length + offset
          < (matchingOfSpineList midWidth prefixAtoms).partner.length := by
        rw [baseLen, Nat.add_assoc midWidth lastCup.leftContext.length offset]
        apply Nat.add_lt_add_left
        have step2 : lastCup.leftContext.length + offset + 2
            < (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2 := by
          rw [Nat.add_right_comm lastCup.leftContext.length offset 2]; exact targetLtTotal
        exact Nat.lt_of_add_lt_add_right step2
      rw [natListGetAt_map_below _ _ _ wPrimeLtBase] at chordAt
      cases Nat.lt_or_ge
          (natListGetAt (matchingOfSpineList midWidth prefixAtoms).partner
            (midWidth + lastCup.leftContext.length + offset))
          (midWidth + lastCup.leftContext.length) with
      | inr isAtOrAbove =>
          rw [freshShiftAbove_ofLe _ _ _ isAtOrAbove] at chordAt
          have expand : midWidth + (lastCup.leftContext.length + 2 + offset) + 1
              = midWidth + lastCup.leftContext.length + offset + 1 + 2 := by
            rw [natSum_middle2 midWidth lastCup.leftContext.length offset]
          rw [expand] at chordAt
          exact natAddRightCancel 2 chordAt
      | inl isBelow =>
          exfalso
          rw [freshShiftAbove_ofNotLe _ _ _ (Nat.not_le.mpr isBelow)] at chordAt
          have zGe : midWidth + lastCup.leftContext.length
              ≤ natListGetAt (matchingOfSpineList midWidth prefixAtoms).partner
                (midWidth + lastCup.leftContext.length + offset) := by
            rw [chordAt]
            exact Nat.le_trans
              (Nat.add_le_add_left
                (Nat.le_trans (Nat.le_add_right _ 2) (Nat.le_add_right _ offset)) midWidth)
              (Nat.le_add_right _ 1)
          exact Nat.not_lt.mpr zGe isBelow

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-mid chord-shift LOCATE descents are built (FC-3 r45, R1).**
`stringMatchingChordShift_below_mid` / `stringMatchingChordShift_above_mid` read forward chords off
`matchingOfSpineList midWidth .partner` and track their survival across the located last-cup drop (below
unshifted, above shifted-down-by-two, the snake position arithmetically excluded), riding the
byte-for-byte-REUSED brick-3 splice `diagramPartner_stepCup` at `seedBoundary := midWidth`.  Two edits over
the r16 width-`0` chord-shifts (the seed `List.range midWidth`; the one new `midWidth ≤ nextFresh` obligation
off `processSpine_nextFresh_le` in the `(Nat.zero_le _)` slot).  Colour-blind; positivity-FREE, so it
SUBSUMES the r16 width-`0` descents.

  What this marker does NOT close (no gate flag flips): the positive-mid pure-cup SORT inhabiting the brick
  `StringPositiveMidPureCupDeterminacy`.  On top of these descents the sort still needs the drop-injectivity
  (`stringDropLastCup_matching_injective_mid`, R2) and the fueled word-threaded locate/sort assembly (R3/R4).
  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip`
  (`StringConvOfMapEqPort`) STAY `false`, and the brick STAYS `def`-open.  `= true`. -/
def fxString_hasPositiveMidChordShift : Bool := true

end FX1Poly.Polygraph
