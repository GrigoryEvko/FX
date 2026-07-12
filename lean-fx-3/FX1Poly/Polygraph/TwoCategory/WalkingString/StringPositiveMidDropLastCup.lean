import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDropLastCup

/-! # WalkingString/StringPositiveMidDropLastCup — dropping a top-of-stack cup is matching-injective at a
POSITIVE mid-width bottom boundary (FC-3 r45, R2)

The width-`0` drop linchpin `stringDropLastCup_matching_injective` / `stringBackAppend_matching_congr`
(`StringMatchingDropLastCup`, r16 PORT 3) cancels a shared last cup downward (appended-equal ⇒ prefix-equal)
and its upward companion.  The positive-mid pure-cup determinacy brick `StringPositiveMidPureCupDeterminacy`
(`StringPositiveMidCupSortResidual`) drives its SORT off `matchingOfSpineList midWidth`, so it needs the SAME
drop-injectivity at the arbitrary `midWidth` bottom boundary — the through-strand survivor count.  This file
ships the two positive-mid siblings.

Both are OFFSET ports (`0 ⤳ midWidth`).  The boundary-partner splice engine `diagramPartner_stepCup` (whose
window partners are the census-free `generalStateCup{Forward,Backward}PartnerMatching`) is `seedBoundary`-
general, and the `WireState`-only per-field congruence body is ALREADY seed-general in the width-`0` file
(`stringExtractDiagram_stepCup_congr`, taking `seedBelowFirst/Second`) — so it is re-copied verbatim here and
called at `seedBoundary := midWidth`.  Two edits over the r16 drop proof:

  * the seed `⟨List.range 0, [], 0, 0⟩ ⤳ ⟨List.range midWidth, [], midWidth, 0⟩`;
  * the ONE new obligation the seed-general splice opens — `midWidth ≤ nextFresh` — discharged in one line by
    the shipped counter monotonicity `processSpine_nextFresh_le` (the seed's `nextFresh` is `midWidth`, and
    the fold never lowers it).  This is the `(Nat.zero_le _)` slot of the width-`0` proof.

Colour-blind throughout: the injection reads only the four `DiagramType` fields, never `F`/`G`/`H`.
Positivity-FREE (subsumes the r16 width-`0` drop at `midWidth := 0`).

Raw Lean 4 + Init; the private range / list / injectivity plumbing is a per-file copy (the codebase
pattern).  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin, `#print axioms` in the independent witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / list / injectivity plumbing (per-file copies, following the codebase pattern) -/

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

/-- `Nat` right-cancellation, propext-free. -/
private theorem addRightCancel : (summand leftValue rightValue : Nat) →
    leftValue + summand = rightValue + summand → leftValue = rightValue
  | 0, _, _, h => h
  | summand + 1, leftValue, rightValue, h => addRightCancel summand leftValue rightValue (Nat.succ.inj h)

/-- `List` append is left-cancellative (structural on the shared front). -/
private theorem appendLeftCancel : (block first second : List Nat) →
    block ++ first = block ++ second → first = second
  | [], _, _, h => h
  | headWire :: rest, first, second, h => by
      have hcons : headWire :: (rest ++ first) = headWire :: (rest ++ second) := h
      injection hcons with _ tailEq
      exact appendLeftCancel rest first second tailEq

private theorem natListInsertAtZeroCancel (block first second : List Nat)
    (h : natListInsertAt first 0 block = natListInsertAt second 0 block) : first = second := by
  rw [natListInsertAt_zero, natListInsertAt_zero] at h
  exact appendLeftCancel block first second h

/-- `natListInsertAt` at a fixed in-range position with a fixed block is left-injective. -/
private theorem natListInsertAt_leftInjective : (position : Nat) → (block first second : List Nat) →
    position ≤ first.length → position ≤ second.length →
    natListInsertAt first position block = natListInsertAt second position block → first = second
  | 0, block, first, second, _, _, h => natListInsertAtZeroCancel block first second h
  | _ + 1, _, [], _, pLe, _, _ => absurd pLe (Nat.not_succ_le_zero _)
  | _ + 1, _, _ :: _, [], _, pLe, _ => absurd pLe (Nat.not_succ_le_zero _)
  | position + 1, block, headFirst :: restFirst, headSecond :: restSecond, pLeFirst, pLeSecond, h => by
      have hcons : headFirst :: natListInsertAt restFirst position block
          = headSecond :: natListInsertAt restSecond position block := h
      injection hcons with hHead hRest
      rw [hHead, natListInsertAt_leftInjective position block restFirst restSecond
        (Nat.le_of_succ_le_succ pLeFirst) (Nat.le_of_succ_le_succ pLeSecond) hRest]

/-- `freshShiftAbove threshold 2` is injective. -/
private theorem freshShiftInjective (threshold a b : Nat)
    (shiftEq : freshShiftAbove threshold 2 a = freshShiftAbove threshold 2 b) : a = b := by
  cases Nat.decLe threshold a with
  | isTrue aGe =>
      cases Nat.decLe threshold b with
      | isTrue bGe =>
          rw [freshShiftAbove_ofLe threshold 2 a aGe, freshShiftAbove_ofLe threshold 2 b bGe] at shiftEq
          exact addRightCancel 2 a b shiftEq
      | isFalse bLt =>
          exfalso
          rw [freshShiftAbove_ofLe threshold 2 a aGe, freshShiftAbove_ofNotLe threshold 2 b bLt] at shiftEq
          have bBelow : b < a + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le bLt) aGe) (Nat.le_add_right a 2)
          rw [shiftEq] at bBelow
          exact Nat.lt_irrefl b bBelow
  | isFalse aLt =>
      cases Nat.decLe threshold b with
      | isTrue bGe =>
          exfalso
          rw [freshShiftAbove_ofNotLe threshold 2 a aLt, freshShiftAbove_ofLe threshold 2 b bGe] at shiftEq
          have aBelow : a < b + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le aLt) bGe) (Nat.le_add_right b 2)
          rw [← shiftEq] at aBelow
          exact Nat.lt_irrefl a aBelow
      | isFalse bLt =>
          rw [freshShiftAbove_ofNotLe threshold 2 a aLt, freshShiftAbove_ofNotLe threshold 2 b bLt] at shiftEq
          exact shiftEq

/-- Mapping `freshShiftAbove threshold 2` over a list is injective. -/
private theorem mapFreshShiftInjective (threshold : Nat) : (first second : List Nat) →
    first.map (freshShiftAbove threshold 2) = second.map (freshShiftAbove threshold 2) → first = second
  | [], [], _ => rfl
  | [], headSecond :: restSecond, h => by
      have hcons : ([] : List Nat)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := h
      injection hcons
  | headFirst :: restFirst, [], h => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = ([] : List Nat) := h
      injection hcons
  | headFirst :: restFirst, headSecond :: restSecond, h => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := h
      injection hcons with hHead hRest
      rw [freshShiftInjective threshold headFirst headSecond hHead,
        mapFreshShiftInjective threshold restFirst restSecond hRest]

/-- The top-count field rises by exactly two through a top-of-stack cup (defeq to `natListInsertAt_length`). -/
private theorem topCount_stepCup (bottomCount : Nat) (state : WireState) (windowPosition : Nat) :
    (extractDiagram bottomCount (stepCup state windowPosition)).topCount
      = (extractDiagram bottomCount state).topCount + 2 :=
  natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]

/-- The partner list has length `bottomCount + openWires`. -/
private theorem extractDiagram_partner_length (bottomCount : Nat) (state : WireState) :
    (extractDiagram bottomCount state).partner.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

/-! ## The positive-mid reduction to a top-of-stack cup (adjoint-triple seed at `midWidth`) -/

/-- Reduce a pure-cup boundary-chained string spine `prefixAtoms ++ [lastCup]` at width `midWidth` to a
top-of-stack cup fired onto the processed prefix, and supply the prefix state's shipped invariants plus the
seed-below-fresh witness (adjoint-triple analogue of `stringDropStepReduce`; the seed-bound is
`processSpine_nextFresh_le`). -/
private theorem stringDropStepReduceMid {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained midWidth (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    matchingOfSpineList midWidth (prefixAtoms ++ [lastCup])
        = extractDiagram midWidth
            (stepCup (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
              lastCup.leftContext.length)
      ∧ WireStateFresh (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms)
      ∧ isUnionFindForest (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).links
      ∧ midWidth ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).nextFresh
      ∧ lastCup.leftContext.length
          ≤ (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms).openWires.length := by
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
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length) lastCup.rightContext.length)
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
    rw [stepAtom_ofCupArity (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ prefixAtoms) lastCup lastDom lastCod]
  exact ⟨structEq, freshS, forestS, seedBelowS, windowFitsS⟩

/-! ## The assembly: dropping a top-of-stack cup is injective on the `midWidth` matching -/

/-- ★ **Dropping a top-of-stack cup is matching-injective at width `midWidth` (the S3 linchpin, positive-mid).**
Two pure-cup boundary-chained string spines over the `midWidth` bottom boundary sharing a last cup with equal
`matchingOfSpineList midWidth` have equal-matching prefixes.  Positive-mid analogue of
`stringDropLastCup_matching_injective`; OFFSET port `0 ⤳ midWidth`. -/
theorem stringDropLastCup_matching_injective_mid {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (firstPrefix secondPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained midWidth (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained midWidth (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (appendedEqual : matchingOfSpineList midWidth (firstPrefix ++ [lastCup])
      = matchingOfSpineList midWidth (secondPrefix ++ [lastCup])) :
    matchingOfSpineList midWidth firstPrefix = matchingOfSpineList midWidth secondPrefix := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, seedBelowFirst, windowFitsFirst⟩ :=
    stringDropStepReduceMid midWidth firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, seedBelowSecond, windowFitsSecond⟩ :=
    stringDropStepReduceMid midWidth secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond] at appendedEqual
  show extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)
    = extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)
  -- per-field inversions
  have eLoops : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).loops
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).loops := by
    have h := congrArg DiagramType.loops appendedEqual
    exact h
  have eBottom : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).bottomCount
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).bottomCount := rfl
  have eTop : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).topCount
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).topCount := by
    have h := congrArg DiagramType.topCount appendedEqual
    rw [topCount_stepCup, topCount_stepCup] at h
    exact addRightCancel 2 _ _ h
  have ePart : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).partner
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).partner := by
    have hMapEq : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).partner.map
          (freshShiftAbove (midWidth + lastCup.leftContext.length) 2)
        = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).partner.map
          (freshShiftAbove (midWidth + lastCup.leftContext.length) 2) := by
      apply natListInsertAt_leftInjective (midWidth + lastCup.leftContext.length)
        [midWidth + lastCup.leftContext.length + 1, midWidth + lastCup.leftContext.length] _ _
        (by rw [mapLength, extractDiagram_partner_length]; exact Nat.add_le_add_left windowFitsFirst midWidth)
        (by rw [mapLength, extractDiagram_partner_length]; exact Nat.add_le_add_left windowFitsSecond midWidth)
      rw [← diagramPartner_stepCup midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)
          lastCup.leftContext.length freshFirst forestFirst seedBelowFirst windowFitsFirst,
        ← diagramPartner_stepCup midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)
          lastCup.leftContext.length freshSecond forestSecond seedBelowSecond windowFitsSecond]
      exact congrArg DiagramType.partner appendedEqual
    exact mapFreshShiftInjective (midWidth + lastCup.leftContext.length) _ _ hMapEq
  show DiagramType.mk
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).bottomCount
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).topCount
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).partner
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).loops
    = DiagramType.mk
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).bottomCount
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).topCount
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).partner
      (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).loops
  rw [eBottom, eTop, ePart, eLoops]

/-! ## The forward matching congruence (the drop's inverse direction) -/

/-- A top-of-stack cup congruence at the `extractDiagram` level (`WireState`-only, re-copied verbatim from
the adjunction's private `extractDiagram_stepCup_congr` — ALREADY seed-general): two fresh, forest-rooted
states with EQUAL `extractDiagram seedBoundary` stay equal after the SAME window's top-of-stack cup. -/
private theorem stringExtractDiagram_stepCup_congr (seedBoundary : Nat)
    (stateFirst stateSecond : WireState) (windowPosition : Nat)
    (freshFirst : WireStateFresh stateFirst) (forestFirst : isUnionFindForest stateFirst.links)
    (freshSecond : WireStateFresh stateSecond) (forestSecond : isUnionFindForest stateSecond.links)
    (seedBelowFirst : seedBoundary ≤ stateFirst.nextFresh)
    (seedBelowSecond : seedBoundary ≤ stateSecond.nextFresh)
    (windowFitsFirst : windowPosition ≤ stateFirst.openWires.length)
    (baseEq : extractDiagram seedBoundary stateFirst = extractDiagram seedBoundary stateSecond) :
    extractDiagram seedBoundary (stepCup stateFirst windowPosition)
      = extractDiagram seedBoundary (stepCup stateSecond windowPosition) := by
  have owEq : stateFirst.openWires.length = stateSecond.openWires.length :=
    congrArg DiagramType.topCount baseEq
  have windowFitsSecond : windowPosition ≤ stateSecond.openWires.length := owEq ▸ windowFitsFirst
  have eBottom : (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).bottomCount
      = (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).bottomCount := rfl
  have eTop : (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).topCount
      = (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).topCount := by
    rw [topCount_stepCup, topCount_stepCup]
    exact congrArg (fun baseTop => baseTop + 2) (congrArg DiagramType.topCount baseEq)
  have eLoops : (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).loops
      = (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).loops := by
    show stateFirst.loops = stateSecond.loops
    exact congrArg DiagramType.loops baseEq
  have ePart : (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).partner
      = (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).partner := by
    rw [diagramPartner_stepCup seedBoundary stateFirst windowPosition freshFirst forestFirst
        seedBelowFirst windowFitsFirst,
      diagramPartner_stepCup seedBoundary stateSecond windowPosition freshSecond forestSecond
        seedBelowSecond windowFitsSecond,
      congrArg DiagramType.partner baseEq]
  show DiagramType.mk
      (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).bottomCount
      (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).topCount
      (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).partner
      (extractDiagram seedBoundary (stepCup stateFirst windowPosition)).loops
    = DiagramType.mk
      (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).bottomCount
      (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).topCount
      (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).partner
      (extractDiagram seedBoundary (stepCup stateSecond windowPosition)).loops
  rw [eBottom, eTop, ePart, eLoops]

/-- ★ **The forward matching congruence at width `midWidth` (the drop's inverse, positive-mid).**  Two
pure-cup boundary-chained string spines over the `midWidth` bottom boundary sharing a last cup whose PREFIXES
have equal `matchingOfSpineList midWidth` also have equal appended `matchingOfSpineList midWidth`.  The upward
companion of `stringDropLastCup_matching_injective_mid`, the back-append the locate needs. -/
theorem stringBackAppend_matching_congr_mid {overallSource overallTarget : adjointTripleGraph.Mode}
    (midWidth : Nat)
    (firstPrefix secondPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained midWidth (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained midWidth (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (prefixEqual : matchingOfSpineList midWidth firstPrefix = matchingOfSpineList midWidth secondPrefix) :
    matchingOfSpineList midWidth (firstPrefix ++ [lastCup])
      = matchingOfSpineList midWidth (secondPrefix ++ [lastCup]) := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, seedBelowFirst, windowFitsFirst⟩ :=
    stringDropStepReduceMid midWidth firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, seedBelowSecond, windowFitsSecond⟩ :=
    stringDropStepReduceMid midWidth secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond]
  exact stringExtractDiagram_stepCup_congr midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix) lastCup.leftContext.length
    freshFirst forestFirst freshSecond forestSecond seedBelowFirst seedBelowSecond
    windowFitsFirst prefixEqual

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the positive-mid drop-injectivity linchpin is built (FC-3 r45, R2).**
`stringDropLastCup_matching_injective_mid` cancels a shared last cup DOWNWARD (appended-equal ⇒ prefix-equal)
and `stringBackAppend_matching_congr_mid` is the UPWARD companion, both riding the byte-for-byte-REUSED splice
`diagramPartner_stepCup` at `seedBoundary := midWidth` and the ALREADY-seed-general per-field congruence
`stringExtractDiagram_stepCup_congr` (re-copied verbatim, called with the `midWidth ≤ nextFresh` witnesses off
`processSpine_nextFresh_le`).  Two edits over the r16 width-`0` drop (the seed `List.range midWidth`; the one
new seed-below-fresh obligation in the `(Nat.zero_le _)` slots).  Colour-blind; positivity-FREE.

  What this marker does NOT close (no gate flag flips): the positive-mid pure-cup SORT inhabiting the brick
  `StringPositiveMidPureCupDeterminacy`.  With R1 (chord-shift descents) + R2 (drop-injectivity) landed, the
  sort still needs the fueled word-threaded locate/sort assembly (R3/R4).  So
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) / `fxString_hasConvOfMapEqPortFlip`
  (`StringConvOfMapEqPort`) STAY `false`, and the brick STAYS `def`-open.  `= true`. -/
def fxString_hasPositiveMidDropLastCup : Bool := true

end FX1Poly.Polygraph
