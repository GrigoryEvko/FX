import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDropLastCup

/-! # WalkingString/StringMatchingDropLastCup — dropping a top-of-stack cup is matching-injective at the
adjoint-triple seed (FC-3 r16, PORT 3)

The walking adjunction's `dropLastCup_matching_injective` (`MatchingDropLastCup`) is the width-`0`
linchpin: two boundary-chained pure-cup spines over the width-`0` bottom boundary sharing a last cup with
EQUAL `matchingOfSpineList 0` have equal-matching prefixes.  Its upward companion `backAppend_matching_congr`
is the drop's inverse (equal prefixes stay equal after a shared cup is appended).  The width-0 pure-cup
sort the string valley split needs (`StringWidthZeroPureCupDeterminacyShared`) is driven by both.

The boundary-partner splice engine `diagramPartner_stepCup` (whose window partners are the census-free
`generalStateCup{Forward,Backward}PartnerMatching`) is `WireState`-only — signature-independent — so it is
REUSED byte-for-byte, no clone.  The port swaps exactly two tokens off the reduction `dropStepReduce`:

  * the cap-tally last-cup-arity read `singletonCupArity` / `capAtomCount_ofAllCupArity`
    (walking-adjunction classifier `adjunctionSpineAtom_isCupOrCap`) → the signature-generic direct
    `AllCupArity`-inversions `allCupArity_lastCup_arity` / `allCupArity_prefix_ofAppend`;
  * the open-wire boundary tracking `processSpine_prefix_openWires_eq_lastDomBoundary` → the shipped
    adjoint-triple `stringProcessSpine_prefix_openWires_eq_lastDomBoundary`.

The `WireState`-only per-field congruence `extractDiagram_stepCup_congr` is `private` in the adjunction
file, so its signature-generic body is re-copied verbatim here (`stringExtractDiagram_stepCup_congr`).
Colour-blind throughout: the injection reads only the four `DiagramType` fields, never `F`/`G`/`H`.

Raw Lean 4 + Init; the private range / list / injectivity plumbing is a per-file copy (the codebase
pattern).  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

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

/-! ## The width-0 reduction to a top-of-stack cup (adjoint-triple seed) -/

/-- Reduce a pure-cup boundary-chained string spine `prefixAtoms ++ [lastCup]` at width `0` to a
top-of-stack cup fired onto the processed prefix, and supply the prefix state's shipped invariants
(adjoint-triple analogue of `dropStepReduce`; the seed-bound is `Nat.zero_le`). -/
private theorem stringDropStepReduce {overallSource overallTarget : adjointTripleGraph.Mode}
    (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    matchingOfSpineList 0 (prefixAtoms ++ [lastCup])
        = extractDiagram 0
            (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
      ∧ WireStateFresh (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
      ∧ isUnionFindForest (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).links
      ∧ lastCup.leftContext.length ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length := by
  obtain ⟨lastDom, lastCod⟩ := allCupArity_lastCup_arity prefixAtoms lastCup pureCup
  have prefixPure : AllCupArity prefixAtoms := allCupArity_prefix_ofAppend prefixAtoms [lastCup] pureCup
  have freshS : WireStateFresh (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) :=
    wireStateFresh_processSpine_ofAllCup prefixAtoms prefixPure ⟨List.range 0, [], 0, 0⟩ (wireStateFresh_initial 0)
  have forestS : isUnionFindForest (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).links :=
    isUnionFindForest_processSpine prefixAtoms ⟨List.range 0, [], 0, 0⟩ isUnionFindForest_nil
  have domLen := stringProcessSpine_prefix_openWires_eq_lastDomBoundary 0 prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length) lastCup.rightContext.length)
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
  exact ⟨structEq, freshS, forestS, windowFitsS⟩

/-! ## The assembly: dropping a top-of-stack cup is injective on the width-0 matching -/

/-- ★ **Dropping a top-of-stack cup is matching-injective at width `0` (the S3 linchpin, adjoint-triple
seed).**  Two pure-cup boundary-chained string spines over the width-`0` bottom boundary sharing a last cup
with equal `matchingOfSpineList 0` have equal-matching prefixes: the last cup fires LAST onto each
processed prefix as a top-of-stack cup, and each `DiagramType` field is a fixed injective image of the
prefix's field (`diagramPartner_stepCup` splices the short chord over the shift, `topCount` adds two,
`bottomCount`/`loops` are `rfl`).  Adjoint-triple analogue of `dropLastCup_matching_injective`. -/
theorem stringDropLastCup_matching_injective {overallSource overallTarget : adjointTripleGraph.Mode}
    (firstPrefix secondPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained 0 (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained 0 (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (appendedEqual : matchingOfSpineList 0 (firstPrefix ++ [lastCup])
      = matchingOfSpineList 0 (secondPrefix ++ [lastCup])) :
    matchingOfSpineList 0 firstPrefix = matchingOfSpineList 0 secondPrefix := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, windowFitsFirst⟩ :=
    stringDropStepReduce firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, windowFitsSecond⟩ :=
    stringDropStepReduce secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond] at appendedEqual
  show extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)
    = extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)
  -- per-field inversions
  have eLoops : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).loops
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).loops := by
    have h := congrArg DiagramType.loops appendedEqual
    exact h
  have eBottom : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).bottomCount
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).bottomCount := rfl
  have eTop : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).topCount
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).topCount := by
    have h := congrArg DiagramType.topCount appendedEqual
    rw [topCount_stepCup, topCount_stepCup] at h
    exact addRightCancel 2 _ _ h
  have ePart : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).partner
      = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).partner := by
    have hMapEq : (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).partner.map
          (freshShiftAbove (0 + lastCup.leftContext.length) 2)
        = (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).partner.map
          (freshShiftAbove (0 + lastCup.leftContext.length) 2) := by
      apply natListInsertAt_leftInjective (0 + lastCup.leftContext.length)
        [0 + lastCup.leftContext.length + 1, 0 + lastCup.leftContext.length] _ _
        (by rw [mapLength, extractDiagram_partner_length]; exact Nat.add_le_add_left windowFitsFirst 0)
        (by rw [mapLength, extractDiagram_partner_length]; exact Nat.add_le_add_left windowFitsSecond 0)
      rw [← diagramPartner_stepCup 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)
          lastCup.leftContext.length freshFirst forestFirst (Nat.zero_le _) windowFitsFirst,
        ← diagramPartner_stepCup 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)
          lastCup.leftContext.length freshSecond forestSecond (Nat.zero_le _) windowFitsSecond]
      exact congrArg DiagramType.partner appendedEqual
    exact mapFreshShiftInjective (0 + lastCup.leftContext.length) _ _ hMapEq
  show DiagramType.mk
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).bottomCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).topCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).partner
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)).loops
    = DiagramType.mk
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).bottomCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).topCount
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).partner
      (extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix)).loops
  rw [eBottom, eTop, ePart, eLoops]

/-! ## The forward matching congruence (the drop's inverse direction) -/

/-- A top-of-stack cup congruence at the `extractDiagram` level (`WireState`-only, re-copied verbatim from
the adjunction's private `extractDiagram_stepCup_congr`): two fresh, forest-rooted states with EQUAL
`extractDiagram seedBoundary` stay equal after the SAME window's top-of-stack cup, each of the four fields
a fixed function of the base (`topCount` +2, `partner` shifted-and-spliced by `diagramPartner_stepCup`,
`bottomCount`/`loops` unchanged).  The second window-fit is read off the shared `topCount`. -/
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

/-- ★ **The forward matching congruence at width `0` (the drop's inverse, adjoint-triple seed).**  Two
pure-cup boundary-chained string spines over the width-`0` bottom boundary sharing a last cup whose
PREFIXES have equal `matchingOfSpineList 0` also have equal appended `matchingOfSpineList 0`: each side
reduces (via `stringDropStepReduce`) to the shared last cup fired as a top-of-stack cup, and
`stringExtractDiagram_stepCup_congr` propagates the prefix equality through that fixed cup step.  The
upward companion of `stringDropLastCup_matching_injective`, the back-append the locate needs. -/
theorem stringBackAppend_matching_congr {overallSource overallTarget : adjointTripleGraph.Mode}
    (firstPrefix secondPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained 0 (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained 0 (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (prefixEqual : matchingOfSpineList 0 firstPrefix = matchingOfSpineList 0 secondPrefix) :
    matchingOfSpineList 0 (firstPrefix ++ [lastCup])
      = matchingOfSpineList 0 (secondPrefix ++ [lastCup]) := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, windowFitsFirst⟩ :=
    stringDropStepReduce firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, windowFitsSecond⟩ :=
    stringDropStepReduce secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond]
  exact stringExtractDiagram_stepCup_congr 0 (processSpine ⟨List.range 0, [], 0, 0⟩ firstPrefix)
    (processSpine ⟨List.range 0, [], 0, 0⟩ secondPrefix) lastCup.leftContext.length
    freshFirst forestFirst freshSecond forestSecond (Nat.zero_le _) (Nat.zero_le _)
    windowFitsFirst prefixEqual

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-0 drop-injectivity linchpin is ported to the adjoint-triple seed (FC-3
r16, PORT 3).**  `stringDropLastCup_matching_injective` cancels a shared last cup DOWNWARD (appended-equal
⇒ prefix-equal) and `stringBackAppend_matching_congr` is the UPWARD companion, both riding the
byte-for-byte-REUSED splice `diagramPartner_stepCup` and re-copied `WireState`-only per-field congruence.
Two token swaps (the generic `allCupArity_lastCup_arity` / `allCupArity_prefix_ofAppend` arity reads + the
shipped `stringProcessSpine_prefix_openWires_eq_lastDomBoundary` tracking) over the width-0 reduction.
Colour-blind; positivity-free.

  What this marker does NOT close (no gate flag flips): the width-0 pure-cup SORT inhabiting
  `StringWidthZeroPureCupDeterminacyShared`.  With PORTS 1/2/3 all landed, the sort still needs the
  word-threaded locate/sort assembly (the W1-W4 word-chain substrate + the shared-top pin) that consumes
  these three ports.  So `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays
  `false`, honestly.  `= true`. -/
def fxString_hasMatchingDropLastCupInjective : Bool := true

end FX1Poly.Polygraph
