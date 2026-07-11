import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDropLastCup

/-! # WalkingString/StringMatchingWidthZeroChordShift — the width-0 chord-shift twins at the
adjoint-triple seed (FC-3 r16, PORT 2)

The walking adjunction's `matchingChordShift_below` / `matchingChordShift_above`
(`MatchingWidthZeroChordShift`) read forward chords off `matchingOfSpineList 0`'s partner list and track
how a chord survives dropping the located last cup: below the window unshifted, above the window shifted
down by two (with the snake position `wlast + 1` arithmetically impossible).  The width-0 pure-cup sort
the string valley split needs (`StringWidthZeroPureCupDeterminacyShared`) drives its locate by exactly
these descents at the adjoint-triple seed.

The whole partner-splice engine the descents ride is `WireState`-only — signature-independent — so it is
REUSED byte-for-byte: `diagramPartner_stepCup` (the shipped brick-3 splice, whose window partners are the
census-free `generalStateCup{Forward,Backward}PartnerMatching`) and `wireStateFresh_processSpine_ofAllCup`
are imported verbatim, no clone.  The port swaps exactly two tokens off the setup:

  * the cap-tally last-cup-arity read `singletonCupArity` / `capAtomCount_ofAllCupArity`
    (walking-adjunction classifier `adjunctionSpineAtom_isCupOrCap`) → the signature-generic direct
    `AllCupArity`-inversions `allCupArity_lastCup_arity` / `allCupArity_prefix_ofAppend`;
  * the open-wire boundary tracking `processSpine_prefix_openWires_eq_lastDomBoundary` → the shipped
    adjoint-triple `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`.

Colour-blind throughout: the descents read partner indices + windows, never `F`/`G`/`H`.

Raw Lean 4 + Init; the private range / map / Nat plumbing is a per-file copy (the codebase pattern).
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / map / Nat plumbing (per-file copy, following the codebase pattern) -/

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

/-- The partner list has length `0 + openWires` (per-file copy of the private
`extractDiagram_partner_length`, specialised to the width-0 seed). -/
private theorem extractDiagram_partner_length_zero (state : WireState) :
    (extractDiagram 0 state).partner.length = 0 + state.openWires.length := by
  show ((List.range (0 + state.openWires.length)).map
      (partnerIndexOf state.links (List.range 0 ++ state.openWires)
        (0 + state.openWires.length))).length = 0 + state.openWires.length
  rw [natListMapLength, rangeLength]

/-! ## The empty-spine forward-chord floor (width-0 trivial) -/

/-- ★ **The empty pure-cup string spine has NO forward chord (adjoint-triple seed, width-0, census-free).**
At width `0` the empty spine's `matchingOf` partner list is EMPTY, so the read at any index is the `0`
fallback, never `0 + targetWindow + 1`.  Adjoint-triple analogue of `emptyMatchingNoForwardChord`: a
`noConfusion` on the fallback zero, no census. -/
private theorem stringEmptyMatchingNoForwardChord
    {overallSource overallTarget : adjointTripleGraph.Mode} (targetWindow : Nat)
    (chordAt : natListGetAt
        (matchingOfSpineList 0
          ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).partner
        (0 + targetWindow)
      = 0 + targetWindow + 1) : False := by
  have partnerNil : (matchingOfSpineList 0
      ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))).partner = [] := rfl
  rw [partnerNil] at chordAt
  have readZero : natListGetAt ([] : List Nat) (0 + targetWindow) = 0 := rfl
  rw [readZero] at chordAt
  exact Nat.noConfusion chordAt

/-! ## The chord-shift setup (rides brick-3 `diagramPartner_stepCup`) -/

/-- The shared setup for the width-0 chord-shift readoffs at the adjoint-triple seed: the last cup folds
onto the processed prefix as a top-of-stack cup, the partner list splices/shifts over the window by the
shipped `diagramPartner_stepCup`, the window fits, and the base partner length reflects. -/
private theorem stringMatchingChordShiftSetup
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    ((matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner
        = natListInsertAt
            ((matchingOfSpineList 0 prefixAtoms).partner.map
              (freshShiftAbove (0 + lastCup.leftContext.length) 2))
            (0 + lastCup.leftContext.length)
            [0 + lastCup.leftContext.length + 1, 0 + lastCup.leftContext.length])
      ∧ lastCup.leftContext.length
          ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length
      ∧ (matchingOfSpineList 0 prefixAtoms).partner.length
          = 0 + (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length := by
  obtain ⟨lastDom, lastCod⟩ := allCupArity_lastCup_arity prefixAtoms lastCup pureCup
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
  refine ⟨?_, windowFitsS, extractDiagram_partner_length_zero _⟩
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
  exact diagramPartner_stepCup 0 (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
    lastCup.leftContext.length freshS forestS (Nat.zero_le _) windowFitsS

/-! ## The chord-shift descents -/

/-- ★ **Chord-shift, below the dropped cup (adjoint-triple seed, width-0, positivity-free).**  A forward
chord `(targetWindow, +1)` in `matchingOf 0 (prefix ++ [lastCup])` at a window strictly below the last
cup's window survives the drop UNSHIFTED into `matchingOf 0 prefix`.  Adjoint-triple analogue of
`matchingChordShift_below`. -/
theorem stringMatchingChordShift_below
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup]))
    (targetWindow : Nat)
    (targetBelow : targetWindow < lastCup.leftContext.length)
    (chordAt : natListGetAt
        (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner
        (0 + targetWindow)
      = 0 + targetWindow + 1) :
    natListGetAt (matchingOfSpineList 0 prefixAtoms).partner
        (0 + targetWindow)
      = 0 + targetWindow + 1 := by
  obtain ⟨partnerSplice, windowFitsS, baseLen⟩ :=
    stringMatchingChordShiftSetup prefixAtoms lastCup chained pureCup
  rw [partnerSplice] at chordAt
  have indexBelowPos : 0 + targetWindow < 0 + lastCup.leftContext.length :=
    Nat.add_lt_add_left targetBelow 0
  have indexBelowLen : 0 + targetWindow
      < ((matchingOfSpineList 0 prefixAtoms).partner.map
          (freshShiftAbove (0 + lastCup.leftContext.length) 2)).length := by
    rw [natListMapLength, baseLen]
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le targetBelow windowFitsS) 0
  have indexBelowBaseLen : 0 + targetWindow
      < (matchingOfSpineList 0 prefixAtoms).partner.length := by
    rw [baseLen]
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le targetBelow windowFitsS) 0
  rw [natListGetAt_natListInsertAt_below _ _ _ _ indexBelowPos indexBelowLen,
    natListGetAt_map_below _ _ _ indexBelowBaseLen] at chordAt
  cases Nat.lt_or_ge
      (natListGetAt (matchingOfSpineList 0 prefixAtoms).partner (0 + targetWindow))
      (0 + lastCup.leftContext.length) with
  | inl isBelow =>
      rw [freshShiftAbove_ofNotLe _ _ _ (Nat.not_le.mpr isBelow)] at chordAt
      exact chordAt
  | inr isAtOrAbove =>
      exfalso
      rw [freshShiftAbove_ofLe _ _ _ isAtOrAbove] at chordAt
      have chainBound : 0 + lastCup.leftContext.length + 2 ≤ 0 + targetWindow + 1 :=
        chordAt ▸ Nat.add_le_add_right isAtOrAbove 2
      have : 0 + lastCup.leftContext.length ≤ 0 + targetWindow :=
        Nat.le_of_succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ 1)) chainBound)
      exact Nat.not_lt.mpr this indexBelowPos

/-- ★ **Chord-shift, above the dropped cup (adjoint-triple seed, width-0, positivity-free).**  A forward
chord `(targetWindow, +1)` in `matchingOf 0 (prefix ++ [lastCup])` at a window strictly above the last
cup's window survives the drop shifted DOWN BY TWO into `matchingOf 0 prefix` at `targetWindow - 2`; the
snake position `targetWindow = wlast + 1` is arithmetically impossible.  Adjoint-triple analogue of
`matchingChordShift_above`. -/
theorem stringMatchingChordShift_above
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup]))
    (targetWindow : Nat)
    (targetAbove : lastCup.leftContext.length < targetWindow)
    (chordAt : natListGetAt
        (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner
        (0 + targetWindow)
      = 0 + targetWindow + 1) :
    natListGetAt (matchingOfSpineList 0 prefixAtoms).partner
        (0 + (targetWindow - 2))
      = 0 + (targetWindow - 2) + 1 := by
  obtain ⟨partnerSplice, windowFitsS, baseLen⟩ :=
    stringMatchingChordShiftSetup prefixAtoms lastCup chained pureCup
  have fullLen : (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner.length
      = (matchingOfSpineList 0 prefixAtoms).partner.length + 2 := by
    rw [partnerSplice, natListInsertAt_length, natListMapLength]
    rfl
  have targetInFull : 0 + targetWindow
      < (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner.length := by
    cases Nat.lt_or_ge (0 + targetWindow)
        (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner.length with
    | inl inRange => exact inRange
    | inr outRange =>
        exfalso
        rw [natListGetAt_zeroOfGe _ _ outRange] at chordAt
        exact Nat.noConfusion chordAt
  have targetLtTotal : targetWindow
      < (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length + 2 := by
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
            ((matchingOfSpineList 0 prefixAtoms).partner.map
              (freshShiftAbove (0 + lastCup.leftContext.length) 2))
            (0 + lastCup.leftContext.length)
            [0 + lastCup.leftContext.length + 1, 0 + lastCup.leftContext.length])
          (0 + (lastCup.leftContext.length + 1))
        = 0 + lastCup.leftContext.length := by
        rw [← Nat.add_assoc 0 lastCup.leftContext.length 1]
        exact natListGetAt_natListInsertAt_inside _ _ _ 1 (Nat.lt_succ_self 1)
          (by rw [natListMapLength, baseLen]; exact Nat.add_le_add_left windowFitsS 0)
      rw [snakeRead] at chordAt
      exact absurd chordAt (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self _)))
  | inr targetAtLeast =>
      obtain ⟨offset, offsetSpec⟩ := Nat.le.dest targetAtLeast
      subst offsetSpec
      rw [partnerSplice] at chordAt
      have windowReduce : lastCup.leftContext.length + 2 + offset - 2 = lastCup.leftContext.length + offset := by
        rw [Nat.add_right_comm lastCup.leftContext.length 2 offset]
        exact natAddSubCancel (lastCup.leftContext.length + offset) 2
      rw [windowReduce, ← Nat.add_assoc 0 lastCup.leftContext.length offset]
      have readEq : natListGetAt
            (natListInsertAt
              ((matchingOfSpineList 0 prefixAtoms).partner.map
                (freshShiftAbove (0 + lastCup.leftContext.length) 2))
              (0 + lastCup.leftContext.length)
              [0 + lastCup.leftContext.length + 1, 0 + lastCup.leftContext.length])
            (0 + (lastCup.leftContext.length + 2 + offset))
          = natListGetAt
              ((matchingOfSpineList 0 prefixAtoms).partner.map
                (freshShiftAbove (0 + lastCup.leftContext.length) 2))
              (0 + lastCup.leftContext.length + offset) := by
        rw [natSum_middle2 0 lastCup.leftContext.length offset]
        exact natListGetAt_natListInsertAt_pastBlock _ _ _ offset
          (by rw [natListMapLength, baseLen]; exact Nat.add_le_add_left windowFitsS 0)
      rw [readEq] at chordAt
      have wPrimeLtBase : 0 + lastCup.leftContext.length + offset
          < (matchingOfSpineList 0 prefixAtoms).partner.length := by
        rw [baseLen, Nat.add_assoc 0 lastCup.leftContext.length offset]
        apply Nat.add_lt_add_left
        have step2 : lastCup.leftContext.length + offset + 2
            < (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length + 2 := by
          rw [Nat.add_right_comm lastCup.leftContext.length offset 2]; exact targetLtTotal
        exact Nat.lt_of_add_lt_add_right step2
      rw [natListGetAt_map_below _ _ _ wPrimeLtBase] at chordAt
      cases Nat.lt_or_ge
          (natListGetAt (matchingOfSpineList 0 prefixAtoms).partner
            (0 + lastCup.leftContext.length + offset))
          (0 + lastCup.leftContext.length) with
      | inr isAtOrAbove =>
          rw [freshShiftAbove_ofLe _ _ _ isAtOrAbove] at chordAt
          have expand : 0 + (lastCup.leftContext.length + 2 + offset) + 1
              = 0 + lastCup.leftContext.length + offset + 1 + 2 := by
            rw [natSum_middle2 0 lastCup.leftContext.length offset]
          rw [expand] at chordAt
          exact natAddRightCancel 2 chordAt
      | inl isBelow =>
          exfalso
          rw [freshShiftAbove_ofNotLe _ _ _ (Nat.not_le.mpr isBelow)] at chordAt
          have zGe : 0 + lastCup.leftContext.length
              ≤ natListGetAt (matchingOfSpineList 0 prefixAtoms).partner
                (0 + lastCup.leftContext.length + offset) := by
            rw [chordAt]
            exact Nat.le_trans
              (Nat.add_le_add_left
                (Nat.le_trans (Nat.le_add_right _ 2) (Nat.le_add_right _ offset)) 0)
              (Nat.le_add_right _ 1)
          exact Nat.not_lt.mpr zGe isBelow

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 chord-shift LOCATE descents are ported to the adjoint-triple seed
(FC-3 r16, PORT 2).**  `stringMatchingChordShift_below` / `stringMatchingChordShift_above` read forward
chords off `matchingOfSpineList 0 .partner` and track their survival across the located last-cup drop
(below unshifted, above shifted-down-by-two, the snake position arithmetically excluded), riding the
byte-for-byte-REUSED brick-3 splice `diagramPartner_stepCup`.  Two token swaps (the generic
`allCupArity_lastCup_arity` / `allCupArity_prefix_ofAppend` arity reads + the shipped
`stringProcessSpine_prefix_openWires_eq_lastDomBoundary` tracking) over the `WireState`-only engine.
Colour-blind; positivity-free; NO `arcDiagram_eq_matching` bridge and NO `0 < bottomCount`.

  What this marker does NOT close (no gate flag flips): the width-0 pure-cup SORT inhabiting
  `StringWidthZeroPureCupDeterminacyShared`.  On top of these descents the sort still needs the
  drop-injectivity (PORT 3) and the word-threaded locate/sort assembly.  So
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false`, honestly.
  `= true`. -/
def fxString_hasMatchingWidthZeroChordShift : Bool := true

end FX1Poly.Polygraph
