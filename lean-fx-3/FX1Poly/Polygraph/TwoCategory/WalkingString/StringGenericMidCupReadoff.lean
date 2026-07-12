import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericWidthArityBridge
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidChordShift
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidSnakeExclusion

/-! # WalkingString — the GENERIC MID-WIDTH CUP READOFF: the positivity-free LOCATE readoff bricks over an
arbitrary adjoint-string CONNECTIVITY signature (FC-4 r6, the readoff tranche of the generic cup-sort driver)

The width-`0` / positive-mid pure-cup SORT's LOCATE recursion rests on three colour-blind readoff facts about
the boundary matching `matchingOfSpineList midWidth`:

  * the LAST cup reads off as an OFFSET short chord `midWidth + w ↦ midWidth + w + 1`
    (`stringMatchingLastCup_isShortChord_mid`, FC-3 r44 P2b);
  * a forward chord BELOW the dropped cup survives UNSHIFTED, ABOVE survives shifted-down-by-two, the snake
    position arithmetically excluded (`stringMatchingChordShift_below_mid` / `..._above_mid`, FC-3 r45 R1);
  * folding a trailing cup grows the processed open-wire count by exactly two
    (`stringMatchingOpenWiresCupEndSplit_mid`, FC-3 r43 P2a).

Every one of these shipped positive-mid bricks is COLOUR-BLIND: the only signature-specific node in each proof
body is the open-wire boundary tracking `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`, and that node
is EXACTLY the r5 B3 generic tracking `genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls`
(`StringGenericWidthArityBridge`).  Every OTHER lemma the bodies call is already `{signature : ModeSignature}`-
generic engine (`generalStateCupForwardPartnerMatching`, `diagramPartner_stepCup`,
`wireStateFresh_processSpine_ofAllCup`, `isUnionFindForest_processSpine`, `processSpine_nextFresh_le`,
`allCupArity_lastCup_arity`, `stepAtom_ofCupArity`, `natListInsertAt_length`, the `natListGetAt`/`freshShiftAbove`
read-offs).  So this file re-founds the three readoff bricks ONCE over the class, verbatim modulo the single
tracking hook.

  * ★ `genericMatchingLastCup_isShortChord_mid cls` — the OFFSET short-chord readoff.
  * ★ `genericMatchingChordShift_below_mid cls` / `genericMatchingChordShift_above_mid cls` — the two descents.
  * ★ `genericMatchingOpenWiresCupEndSplit_mid` — the cup-end open-wire split, `{signature}`-generic (it needs
    NO connectivity field — it reads only the cup arity through `stepAtom_ofCupArity` + the insert length).

Positivity-FREE throughout (RECON finding): none of the three reads the involution, so none needs `0 < midWidth`;
each generic statement SUBSUMES the r16 width-`0` readoff at `midWidth := 0`.  The `0 < midWidth` the doubly-
positive wall consumes enters LATER, at the snake exclusion (`stringMatchingForwardChordsNotAdjacent_mid`, which
rides the positive-bottom-boundary involution) — the named r7 residual, NOT this tranche.

## The HONESTY LAW — each generic brick FIRED at `k = 2` (recovering the NAMED shipped lemma) AND `k = 3`

  * ★ `k = 2` recovery — each generic brick at `adjointStringConnectivityAtTwo` re-derives the NAMED shipped
    positive-mid lemma on the nose (the shipped lemma and the generic-at-two BOTH inhabit the named statement;
    `adjointStringConnectivityAtTwo.signature` is DEFEQ to `adjointTripleModeSignature`, so the recovery is a
    definitional identity, not a coincidence).
  * ★ `k = 3` fire — each generic brick at `adjointStringConnectivityAtThree` fires on a genuine adjoint-
    quadruple cup: the short-chord on a POSITIVE-mid single-survivor quad cup (structural), the cup-end split on
    a width-0 quad cup (structural), the chord-shifts on genuine quad two-cup fixtures (window-below / window-
    above), each cross-checked against the genuinely-COMPUTED partner list.
  * ★ negative control — `SpineTraceEquiv.refl` is NOT what these readoffs compute; the chord-shift descents
    genuinely relocate a chord (a non-identity read).

## The FLIP LAW — this tranche does NOT flip the census

This lands the positivity-FREE readoff tranche of the generic cup-sort driver.  The census marker
`fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) STAYS `false`: its bill is the FULL
width-`0` quad SORT, which additionally needs the generic snake exclusion (through the generic positive-boundary
involution), the generic drop-injectivity, the generic fueled LOCATE, the generic fueled SORT DRIVER, and the
`k = 3` decision — the NAMED r7 residual.  This file records exactly what ships in
`fxString_hasGenericMidCupReadoff`.

ADDITIVE ONLY: no shipped WalkingString file is touched; the FROZEN positive-mid bricks and the r5 class/bridge
are CONSUMED, never edited.  Raw Lean 4 + Init; the private range/map/Nat plumbing is a per-file copy (the
codebase pattern), the readoffs are the FROZEN proofs with the tracking hook swapped for the class-generic one,
the recoveries are `abbrev`-inhabited, the fires are concrete `SpineBoundaryChained` / `by decide` partner
certificates; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin plus an INDEPENDENT `#print axioms` witness. -/

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
  rw [rangeLoopLength count []]; exact Nat.add_zero count

private theorem natListMapLength (mapFunction : Nat → Nat) :
    (list : List Nat) → (list.map mapFunction).length = list.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (natListMapLength mapFunction rest)

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

private theorem natListGetAt_zeroOfGe :
    (list : List Nat) → (index : Nat) → list.length ≤ index → natListGetAt list index = 0
  | [], _, _ => rfl
  | _ :: _, 0, atLeast => absurd atLeast (Nat.not_succ_le_zero _)
  | _ :: rest, index + 1, atLeast =>
      natListGetAt_zeroOfGe rest index (Nat.le_of_succ_le_succ atLeast)

private theorem genericReadoffNatAddRightCancel :
    (added : Nat) → {leftSide rightSide : Nat} →
    leftSide + added = rightSide + added → leftSide = rightSide
  | 0, _, _, sumsEqual => sumsEqual
  | added + 1, _, _, sumsEqual => genericReadoffNatAddRightCancel added (Nat.succ.inj sumsEqual)

private theorem natAddSubCancel (baseValue : Nat) : (subtracted : Nat) →
    baseValue + subtracted - subtracted = baseValue
  | 0 => rfl
  | subtracted + 1 => by
      rw [Nat.add_succ, Nat.succ_sub_succ]
      exact natAddSubCancel baseValue subtracted

private theorem natSum_middle2 (leftValue midValue rightValue : Nat) :
    leftValue + (midValue + 2 + rightValue) = leftValue + midValue + rightValue + 2 := by
  rw [Nat.add_right_comm midValue 2 rightValue, ← Nat.add_assoc leftValue (midValue + rightValue) 2,
    ← Nat.add_assoc leftValue midValue rightValue]

/-- The partner list has length `midWidth + openWires` (per-file copy of the private
`extractDiagram_partner_length`, at the positive-mid seed). -/
private theorem extractDiagram_partner_length_mid (midWidth : Nat) (state : WireState) :
    (extractDiagram midWidth state).partner.length = midWidth + state.openWires.length := by
  show ((List.range (midWidth + state.openWires.length)).map
      (partnerIndexOf state.links (List.range midWidth ++ state.openWires)
        (midWidth + state.openWires.length))).length = midWidth + state.openWires.length
  rw [natListMapLength, rangeLength]

/-! ## Brick 1 — the generic OFFSET short-chord readoff (the tracking hook swapped for the class-generic one) -/

/-- ★★ **The last cup of a pure-cup string spine reads off as a short chord on `matchingOfSpineList midWidth`,
over an arbitrary adjoint-string CONNECTIVITY signature (positive-mid, positivity-free).**  The FROZEN FC-3 r44
`stringMatchingLastCup_isShortChord_mid` proof, generic over the class: the ONLY signature-specific node — the
open-wire boundary tracking — is the r5 B3 `genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls`;
everything else is `{signature}`-generic engine.  The last atom of a boundary-chained pure-cup spine fires LAST,
so nothing has split its two legs: window `w = lastCup.leftContext.length` matches the OFFSET index
`midWidth + w` to `midWidth + w + 1`. -/
theorem genericMatchingLastCup_isShortChord_mid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
    (chained : SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    natListGetAt (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner
        (midWidth + lastCup.leftContext.length)
      = midWidth + lastCup.leftContext.length + 1 := by
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
  have domLen := genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls midWidth prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  have partnerEq := generalStateCupForwardPartnerMatching midWidth
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup.leftContext.length
    forestS freshS seedBelowS windowFitsS
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
  exact partnerEq

/-! ## The chord-shift setup + descents (the tracking hook swapped for the class-generic one) -/

/-- The shared setup for the positive-mid chord-shift readoffs, generic over the class.  The FROZEN FC-3 r45
`stringMatchingChordShiftSetupMid` proof with the tracking hook swapped for
`genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls`. -/
private theorem genericMatchingChordShiftSetupMid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
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
  have domLen := genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls midWidth prefixAtoms lastCup chained
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

/-- ★★ **Chord-shift, below the dropped cup, over the class (positive-mid, positivity-free).**  The FROZEN FC-3
r45 `stringMatchingChordShift_below_mid` proof, generic over the class (the tracking hook rides the setup).  A
forward chord `(targetWindow, +1)` at a window strictly below the last cup's window survives the drop
UNSHIFTED. -/
theorem genericMatchingChordShift_below_mid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
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
    genericMatchingChordShiftSetupMid cls midWidth prefixAtoms lastCup chained pureCup
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
      have aboveTarget : midWidth + lastCup.leftContext.length ≤ midWidth + targetWindow :=
        Nat.le_of_succ_le_succ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right _ 1)) chainBound)
      exact Nat.not_lt.mpr aboveTarget indexBelowPos

/-- ★★ **Chord-shift, above the dropped cup, over the class (positive-mid, positivity-free).**  The FROZEN FC-3
r45 `stringMatchingChordShift_above_mid` proof, generic over the class.  A forward chord `(targetWindow, +1)` at
a window strictly above the last cup's window survives the drop shifted DOWN BY TWO; the snake position
`targetWindow = wlast + 1` is arithmetically impossible. -/
theorem genericMatchingChordShift_above_mid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
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
    genericMatchingChordShiftSetupMid cls midWidth prefixAtoms lastCup chained pureCup
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
          exact genericReadoffNatAddRightCancel 2 chordAt
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

/-! ## Brick 3 — the cup-end open-wire split (`{signature}`-generic; needs NO connectivity field) -/

/-- ★★ **Folding a trailing cup onto a pure-cup spine grows the processed open-wire count by exactly two, at the
`midWidth` seed, over an arbitrary mode signature.**  The FROZEN FC-3 r43 `stringMatchingOpenWiresCupEndSplit_mid`
proof; it reads ONLY the cup's arity through `stepAtom_ofCupArity` and the insert length `natListInsertAt_length`,
both `{signature}`-generic and seed-agnostic — so it needs neither the connectivity field nor positivity.
Subsumes the shipped triple version at `signature := adjointTripleModeSignature`. -/
theorem genericMatchingOpenWiresCupEndSplit_mid {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom signature overallSource overallTarget))
    (lastCup : SpineAtom signature overallSource overallTarget)
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ (prefixAtoms ++ [lastCup])).openWires.length
      = (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2 := by
  obtain ⟨lastDom, lastCod⟩ := allCupArity_lastCup_arity prefixAtoms lastCup pureCup
  rw [processSpine_append prefixAtoms [lastCup] ⟨List.range midWidth, [], midWidth, 0⟩]
  show (stepAtom (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup).openWires.length
    = (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2
  rw [stepAtom_ofCupArity (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup
    lastDom lastCod]
  exact natListInsertAt_length (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires
    lastCup.leftContext.length
    [(processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh,
      (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh + 1]

/-! ## `k = 2` RECOVERY — each generic brick re-derives the NAMED shipped positive-mid lemma -/

/-- The statement of the shipped `k = 2` short-chord readoff, named as the recovery TARGET. -/
abbrev StringShortChordMidStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]) →
    AllCupArity (prefixAtoms ++ [lastCup]) →
    natListGetAt (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner
        (midWidth + lastCup.leftContext.length)
      = midWidth + lastCup.leftContext.length + 1

/-- ★ **The shipped `k = 2` short-chord inhabits the named statement.** -/
theorem stringShortChordMid_shippedInhabitant : StringShortChordMidStatement :=
  @stringMatchingLastCup_isShortChord_mid

/-- ★★ **The generic short-chord, at `k = 2`, RE-DERIVES the shipped short-chord** (defeq consumption check:
`adjointStringConnectivityAtTwo.signature` is `adjointTripleModeSignature`). -/
theorem stringShortChordMid_viaGenericClassAtTwo : StringShortChordMidStatement :=
  fun midWidth prefixAtoms lastCup chained pureCup =>
    genericMatchingLastCup_isShortChord_mid adjointStringConnectivityAtTwo
      midWidth prefixAtoms lastCup chained pureCup

/-- The statement of the shipped `k = 2` below-descent, named as the recovery TARGET. -/
abbrev StringChordShiftBelowMidStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]) →
    AllCupArity (prefixAtoms ++ [lastCup]) →
    ∀ (targetWindow : Nat), targetWindow < lastCup.leftContext.length →
    natListGetAt (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner (midWidth + targetWindow)
        = midWidth + targetWindow + 1 →
    natListGetAt (matchingOfSpineList midWidth prefixAtoms).partner (midWidth + targetWindow)
      = midWidth + targetWindow + 1

/-- ★ **The shipped `k = 2` below-descent inhabits the named statement.** -/
theorem stringChordShiftBelowMid_shippedInhabitant : StringChordShiftBelowMidStatement :=
  @stringMatchingChordShift_below_mid

/-- ★★ **The generic below-descent, at `k = 2`, RE-DERIVES the shipped below-descent.** -/
theorem stringChordShiftBelowMid_viaGenericClassAtTwo : StringChordShiftBelowMidStatement :=
  fun midWidth prefixAtoms lastCup chained pureCup targetWindow targetBelow chordAt =>
    genericMatchingChordShift_below_mid adjointStringConnectivityAtTwo
      midWidth prefixAtoms lastCup chained pureCup targetWindow targetBelow chordAt

/-- The statement of the shipped `k = 2` above-descent, named as the recovery TARGET. -/
abbrev StringChordShiftAboveMidStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]) →
    AllCupArity (prefixAtoms ++ [lastCup]) →
    ∀ (targetWindow : Nat), lastCup.leftContext.length < targetWindow →
    natListGetAt (matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])).partner (midWidth + targetWindow)
        = midWidth + targetWindow + 1 →
    natListGetAt (matchingOfSpineList midWidth prefixAtoms).partner (midWidth + (targetWindow - 2))
      = midWidth + (targetWindow - 2) + 1

/-- ★ **The shipped `k = 2` above-descent inhabits the named statement.** -/
theorem stringChordShiftAboveMid_shippedInhabitant : StringChordShiftAboveMidStatement :=
  @stringMatchingChordShift_above_mid

/-- ★★ **The generic above-descent, at `k = 2`, RE-DERIVES the shipped above-descent.** -/
theorem stringChordShiftAboveMid_viaGenericClassAtTwo : StringChordShiftAboveMidStatement :=
  fun midWidth prefixAtoms lastCup chained pureCup targetWindow targetAbove chordAt =>
    genericMatchingChordShift_above_mid adjointStringConnectivityAtTwo
      midWidth prefixAtoms lastCup chained pureCup targetWindow targetAbove chordAt

/-- The statement of the shipped `k = 2` cup-end split, named as the recovery TARGET. -/
abbrev StringCupEndSplitMidStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    AllCupArity (prefixAtoms ++ [lastCup]) →
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ (prefixAtoms ++ [lastCup])).openWires.length
      = (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length + 2

/-- ★ **The shipped `k = 2` cup-end split inhabits the named statement.** -/
theorem stringCupEndSplitMid_shippedInhabitant : StringCupEndSplitMidStatement :=
  @stringMatchingOpenWiresCupEndSplit_mid

/-- ★★ **The generic cup-end split, at `signature := adjointTripleModeSignature`, RE-DERIVES the shipped split.** -/
theorem stringCupEndSplitMid_viaGenericSignatureAtTwo : StringCupEndSplitMidStatement :=
  fun midWidth prefixAtoms lastCup pureCup =>
    genericMatchingOpenWiresCupEndSplit_mid midWidth prefixAtoms lastCup pureCup

/-! ## `k = 3` FIRES — the generic bricks run on genuine adjoint-quadruple cups

The `k = 3` fixtures ride the fresh adjoint-QUADRUPLE seed (`adjointQuadrupleModeSignature`, six generators, the
letter `L4` absent from the `k = 2` alphabet). -/

/-- A genuine `k = 3` mid-`1` pure-cup last cup: the unit `η1` (`id_base ⇒ L1·L2`, window `0`) riding a SINGLE
survivor through-strand `L1 : base ⟶ tip` on the right, so its window is `0` and its dom-boundary width is `1`
(the one survivor).  The through-strand re-ranking a width-`0` readoff never exercises. -/
def quadMidOneCupOverL1 :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.tip where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext :=
    ModalityPath.cons AdjointQuadrupleModality.letterOne
      (ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.tip)

/-- The mid-`1` `k = 3` boundary matching computes to `[3, 2, 1, 0]`: the single survivor `0` links top-to-bottom
(`0 ↔ 3`), and the cup's two fresh legs sit at boundary indices `1, 2` ABOVE the survivor (`1 ↔ 2`). -/
theorem quadMidOneCupOverL1_matchingComputes :
    (matchingOfSpineList 1 [quadMidOneCupOverL1]).partner = [3, 2, 1, 0] := by decide

/-- ★ **The generic short-chord FIRES at `k = 3`, mid-`1`.**  `genericMatchingLastCup_isShortChord_mid` at
`adjointStringConnectivityAtThree`, `midWidth = 1`, on the single-survivor quad cup reads its window `0` off
`matchingOfSpineList 1`'s partner list at the OFFSET index `1 + 0 = 1`, matching `2` — agreeing with the
genuinely-computed `partner[1] = 2`.  Structural fire (every chaining / arity hypothesis is `rfl`); the offset is
genuinely `midWidth = 1` above the survivor — the through-strand re-ranking a width-`0` readoff never exercises. -/
theorem genericShortChordMid_firesAtThree :
    natListGetAt (matchingOfSpineList 1 [quadMidOneCupOverL1]).partner 1 = 2 :=
  genericMatchingLastCup_isShortChord_mid adjointStringConnectivityAtThree 1 [] quadMidOneCupOverL1
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))
    (AllCupArity.cons rfl rfl AllCupArity.nil)

/-- A genuine `k = 3` width-`0` cup, the unit `η1` (`id_base ⇒ L1·L2`), for the cup-end split fire. -/
def quadCupEndFixture :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- ★ **The generic cup-end split FIRES at `k = 3`.**  Folding the width-`0` quad cup `η1` onto the empty prefix
grows the processed open-wire count by exactly two — a structural non-vacuous witness at three colours. -/
theorem genericCupEndSplit_firesAtThree :
    (processSpine ⟨List.range 0, [], 0, 0⟩ [quadCupEndFixture]).openWires.length
      = (processSpine ⟨List.range 0, [], 0, 0⟩
          ([] : List (SpineAtom adjointQuadrupleModeSignature
            AdjointQuadrupleMode.base AdjointQuadrupleMode.base))).openWires.length + 2 :=
  genericMatchingOpenWiresCupEndSplit_mid 0 [] quadCupEndFixture (AllCupArity.cons rfl rfl AllCupArity.nil)

/-- A `k = 3` cup at window `2` (leftContext `L1·L2`, length `2`), the LAST cup of the below-fixture. -/
def quadCupWindowTwo :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := quadL1L2
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- The `k = 3` two-cup below-fixture `[η1@0, η1@2]`: an inner cup at window `0` and a last cup at window `2`
above it, so the inner cup's chord `(0, 1)` sits strictly BELOW the last cup's window. -/
def quadBelowFixture :
    List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base) :=
  [quadCupEndFixture, quadCupWindowTwo]

/-- The below-fixture's full matching computes to `[1, 0, 3, 2]` (chords at windows `0` and `2`). -/
theorem quadBelowFixture_matchingComputes :
    (matchingOfSpineList 0 quadBelowFixture).partner = [1, 0, 3, 2] := by decide

/-- The below-fixture's PREFIX matching (drop the last cup) computes to `[1, 0]`. -/
theorem quadBelowPrefix_matchingComputes :
    (matchingOfSpineList 0 [quadCupEndFixture]).partner = [1, 0] := by decide

/-- ★ **The generic below-descent FIRES at `k = 3`.**  On the two-cup fixture, the forward chord at window `0`
(strictly below the last cup's window `2`) survives dropping the last cup UNSHIFTED: `partner[0] = 1` in the full
matching maps to `partner[0] = 1` in the prefix.  The `chordAt` hypothesis is the genuinely-computed
`partner[0] = 1` (`by decide`), the below-window witness `0 < 2` is `by decide`; the conclusion agrees with
`quadBelowPrefix_matchingComputes`. -/
theorem genericChordShiftBelowMid_firesAtThree :
    natListGetAt (matchingOfSpineList 0 [quadCupEndFixture]).partner 0 = 1 :=
  genericMatchingChordShift_below_mid adjointStringConnectivityAtThree 0 [quadCupEndFixture] quadCupWindowTwo
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    0 (by decide)
    (by decide)

/-- A `k = 3` cup at window `0` riding TWO right strands `L1·L2` (rightContext length `2`), the LAST cup of the
above-fixture: it fires at window `0` with a chord ABOVE it (the inner cup's chord, shifted up by two). -/
def quadCupWindowZeroRideTwo :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := quadL1L2

/-- The `k = 3` two-cup above-fixture `[η1@0, η1@0-ride-2]`: an inner cup at window `0` and a last cup at window
`0` riding two right strands, so the inner cup's chord sits at window `2`, strictly ABOVE the last cup's window. -/
def quadAboveFixture :
    List (SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base) :=
  [quadCupEndFixture, quadCupWindowZeroRideTwo]

/-- The above-fixture's full matching computes to `[1, 0, 3, 2]` (last cup's chord at window `0`, inner cup's
chord shifted up to window `2`). -/
theorem quadAboveFixture_matchingComputes :
    (matchingOfSpineList 0 quadAboveFixture).partner = [1, 0, 3, 2] := by decide

/-- ★ **The generic above-descent FIRES at `k = 3`.**  On the two-cup fixture, the forward chord at window `2`
(strictly above the last cup's window `0`) survives dropping the last cup shifted DOWN BY TWO to window `0`:
`partner[2] = 3` in the full matching maps to `partner[0] = 1` in the prefix.  The `chordAt` hypothesis is the
genuinely-computed `partner[2] = 3` (`by decide`), the above-window witness `0 < 2` is `by decide`; the
conclusion agrees with `quadBelowPrefix_matchingComputes`. -/
theorem genericChordShiftAboveMid_firesAtThree :
    natListGetAt (matchingOfSpineList 0 [quadCupEndFixture]).partner 0 = 1 :=
  genericMatchingChordShift_above_mid adjointStringConnectivityAtThree 0 [quadCupEndFixture]
    quadCupWindowZeroRideTwo
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    2 (by decide)
    (by decide)

/-! ## Negative control — the readoffs are NOT the identity read -/

/-- ★ **Negative control: the mid-`1` short chord is a genuine relocation, not a fixed point.**  The
short-chord fire reads `partner[1] = 2 ≠ 1`: the boundary port `1` is matched to a DISTINCT partner, so the
readoff is non-trivial (it is not the vacuous `partner[i] = i`). -/
theorem genericShortChordMid_firesAtThree_notFixed :
    natListGetAt (matchingOfSpineList 1 [quadMidOneCupOverL1]).partner 1 ≠ 1 := by
  rw [genericShortChordMid_firesAtThree]; decide

/-! ## Road marker -/

/-- **★ ESTABLISHED — the generic mid-width cup READOFF tranche is machine-checked (FC-4 r6, the positivity-free
readoff bricks of the generic cup-sort driver).**  The three shipped positive-mid LOCATE readoffs re-founded ONCE
over `AdjointStringConnectivity × midWidth`, verbatim modulo the single signature-specific node — the r5 B3
generic open-wire tracking `genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls`:

  * `genericMatchingLastCup_isShortChord_mid cls` — the OFFSET short-chord readoff;
  * `genericMatchingChordShift_below_mid cls` / `genericMatchingChordShift_above_mid cls` — the two descents;
  * `genericMatchingOpenWiresCupEndSplit_mid` — the cup-end split (`{signature}`-generic; no connectivity field).

The HONESTY LAW discharged: each generic brick recovers the NAMED shipped `k = 2` positive-mid lemma on the nose
(`..._shippedInhabitant` / `..._viaGenericClassAtTwo`, defeq at `adjointStringConnectivityAtTwo`) AND fires at
`k = 3` on genuine adjoint-quadruple cups — the short-chord on a POSITIVE-mid single-survivor cup
(`genericShortChordMid_firesAtThree`, cross-checked `[3,2,1,0]`), the cup-end split on a width-`0` cup
(`genericCupEndSplit_firesAtThree`), the descents on genuine quad two-cup fixtures
(`genericChordShiftBelowMid_firesAtThree` / `...AboveMid...`, cross-checked `[1,0,3,2] / [1,0]`) — with a negative
control (`..._notFixed`) confirming the readoffs are genuine relocations.

  What this marker does NOT close (THE FLIP LAW, honest round boundary): the census marker
  `fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) STAYS `false`.  Its bill is the FULL
  width-`0` quad SORT, which ON TOP of this readoff tranche additionally needs, over `cls × midWidth`:

    (r7-1) the generic SNAKE EXCLUSION `stringMatchingForwardChordsNotAdjacent_mid` — the ONE node that consumes
      `0 < midWidth`, riding the positive-bottom-boundary involution `stringMatchingOf_partner_isInvolution`,
      whose generic port must re-found the arc-carrier census/perfect-matching tower
      (`stringArcBoundaryCensus_ofChainedSpineList`, `stringArcPerfectMatchingTokens_ofChainedSpineList`) over the
      class through the already-generic `arcDiagram_eq_matching` bridge;
    (r7-2) the generic DROP-INJECTIVITY `stringDropLastCup_matching_injective_mid` + `..._backAppend_congr`;
    (r7-3) the generic fueled LOCATE `stringMatchingLocateAuxMid` (consuming the snake exclusion);
    (r7-4) the generic fueled SORT DRIVER + `GenericPositiveMidPureCupDeterminacy`, recovering the shipped
      `stringPositiveMidPureCupDeterminacy_proof` / `stringWidthZeroPureCupDeterminacyShared_proof` at `k = 2`;
    (r7-5) the `k = 3` end-to-end SORT decision.

  These five are the NAMED r7 residual.  `= true`. -/
def fxString_hasGenericMidCupReadoff : Bool := true

end FX1Poly.Polygraph
