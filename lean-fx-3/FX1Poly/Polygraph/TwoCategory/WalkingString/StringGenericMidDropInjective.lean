import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericWidthArityBridge
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPositiveMidDropLastCup

/-! # WalkingString — the GENERIC MID-WIDTH DROP-INJECTIVITY: dropping a top-of-stack cup is matching-injective
over an arbitrary adjoint-string CONNECTIVITY signature (FC-4 r6, the drop tranche of the generic cup-sort driver)

The width-`0` / positive-mid pure-cup SORT's peel step rests on the DROP LINCHPIN: dropping a shared top-of-stack
cup is matching-injective (`stringDropLastCup_matching_injective_mid`, FC-3 r45 R2 — appended-equal ⇒ prefix-equal)
with its upward companion (`stringBackAppend_matching_congr_mid` — prefix-equal ⇒ appended-equal).  The driver
consumes exactly the downward direction to cancel the located cup and recurse on the shorter spines.

Both shipped bricks are COLOUR-BLIND: the injection reads only the four `DiagramType` fields, never `F`/`G`/`H`.
The ONLY signature-specific node in each proof body is the open-wire boundary tracking
`stringProcessSpine_prefix_openWires_eq_lastDomBoundary`, and that node is EXACTLY the r5 B3 generic tracking
`genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls` (`StringGenericWidthArityBridge`).  Every OTHER lemma
the bodies call is already `{signature}`-generic engine (`diagramPartner_stepCup`, the per-field `DiagramType`
projections, `natListInsertAt_leftInjective`, `mapFreshShiftInjective`, `topCount_stepCup`,
`extractDiagram_partner_length`).  So this file re-founds the two drop bricks ONCE over the class, verbatim modulo
the single tracking hook.

  * ★ `genericDropLastCup_matching_injective_mid cls` — the DOWNWARD drop-injectivity linchpin (the peel step).
  * ★ `genericBackAppend_matching_congr_mid cls` — the UPWARD companion (the re-append the locate needs).

Positivity-FREE (RECON finding): the injection reads only `DiagramType` fields, never the involution, so neither
needs `0 < midWidth`; each generic statement SUBSUMES the r16 width-`0` drop at `midWidth := 0`.  The `0 < midWidth`
the doubly-positive wall consumes enters LATER, at the snake exclusion — the named r7 residual, NOT this tranche.

## The HONESTY LAW — each generic brick FIRED at `k = 2` (recovering the NAMED shipped lemma) AND `k = 3`

  * ★ `k = 2` recovery — each generic brick at `adjointStringConnectivityAtTwo` re-derives the NAMED shipped
    positive-mid drop lemma on the nose (`..._shippedInhabitant` / `..._viaGenericClassAtTwo`, defeq at
    `adjointStringConnectivityAtTwo`).
  * ★ `k = 3` fire — each generic brick at `adjointStringConnectivityAtThree` fires on a GENUINELY DISTINCT pair of
    adjoint-quadruple spines: `η1` (`id_base ⇒ L1·L2`) and `η3` (`id_base ⇒ L3·L4`, the fresh letter `L4`) are
    DISTINCT cup generators with IDENTICAL arities, so the two window-`0` prefixes `[η1]` / `[η3]` are distinct
    spines that the matching (which ignores generator identity) cannot tell apart — the exact shape the drop
    injectivity discriminates.  The shared last cup is a genuine `k = 3` window-`2` cup.

## The FLIP LAW — this tranche does NOT flip the census

Lands the positivity-FREE drop tranche of the generic cup-sort driver.  The census marker
`fxString_hasNColourAtomPinReroute` STAYS `false`: its bill is the FULL width-`0` quad SORT, which additionally
needs the generic snake exclusion (through the generic positive-boundary involution), the generic fueled LOCATE,
the generic fueled SORT DRIVER, and the `k = 3` decision — the NAMED r7 residual.  Recorded in
`fxString_hasGenericMidDropInjective`.

ADDITIVE ONLY: no shipped WalkingString file is touched.  Raw Lean 4 + Init; the private range / list /
injectivity plumbing is a per-file copy (the codebase pattern), the drop bodies are the FROZEN proofs with the
tracking hook swapped for the class-generic one; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-
free.  Per-declaration `#assert_no_axioms` gated in the audit twin plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / list / injectivity plumbing (per-file copies, following the codebase pattern; the two
`addRightCancel`-family names carry a distinct prefix because public twins live in the import closure) -/

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

private theorem genericDropNatAddRightCancel : (summand leftValue rightValue : Nat) →
    leftValue + summand = rightValue + summand → leftValue = rightValue
  | 0, _, _, sumsEqual => sumsEqual
  | summand + 1, leftValue, rightValue, sumsEqual =>
      genericDropNatAddRightCancel summand leftValue rightValue (Nat.succ.inj sumsEqual)

private theorem appendLeftCancel : (block first second : List Nat) →
    block ++ first = block ++ second → first = second
  | [], _, _, appendEq => appendEq
  | headWire :: rest, first, second, appendEq => by
      have hcons : headWire :: (rest ++ first) = headWire :: (rest ++ second) := appendEq
      injection hcons with _ tailEq
      exact appendLeftCancel rest first second tailEq

private theorem natListInsertAtZeroCancel (block first second : List Nat)
    (insertEq : natListInsertAt first 0 block = natListInsertAt second 0 block) : first = second := by
  rw [natListInsertAt_zero, natListInsertAt_zero] at insertEq
  exact appendLeftCancel block first second insertEq

private theorem natListInsertAt_leftInjective : (position : Nat) → (block first second : List Nat) →
    position ≤ first.length → position ≤ second.length →
    natListInsertAt first position block = natListInsertAt second position block → first = second
  | 0, block, first, second, _, _, insertEq => natListInsertAtZeroCancel block first second insertEq
  | _ + 1, _, [], _, positionLe, _, _ => absurd positionLe (Nat.not_succ_le_zero _)
  | _ + 1, _, _ :: _, [], _, positionLe, _ => absurd positionLe (Nat.not_succ_le_zero _)
  | position + 1, block, headFirst :: restFirst, headSecond :: restSecond, positionLeFirst, positionLeSecond,
      insertEq => by
      have hcons : headFirst :: natListInsertAt restFirst position block
          = headSecond :: natListInsertAt restSecond position block := insertEq
      injection hcons with hHead hRest
      rw [hHead, natListInsertAt_leftInjective position block restFirst restSecond
        (Nat.le_of_succ_le_succ positionLeFirst) (Nat.le_of_succ_le_succ positionLeSecond) hRest]

private theorem freshShiftInjective (threshold leftValue rightValue : Nat)
    (shiftEq : freshShiftAbove threshold 2 leftValue = freshShiftAbove threshold 2 rightValue) :
    leftValue = rightValue := by
  cases Nat.decLe threshold leftValue with
  | isTrue leftGe =>
      cases Nat.decLe threshold rightValue with
      | isTrue rightGe =>
          rw [freshShiftAbove_ofLe threshold 2 leftValue leftGe,
            freshShiftAbove_ofLe threshold 2 rightValue rightGe] at shiftEq
          exact genericDropNatAddRightCancel 2 leftValue rightValue shiftEq
      | isFalse rightLt =>
          exfalso
          rw [freshShiftAbove_ofLe threshold 2 leftValue leftGe,
            freshShiftAbove_ofNotLe threshold 2 rightValue rightLt] at shiftEq
          have rightBelow : rightValue < leftValue + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le rightLt) leftGe)
              (Nat.le_add_right leftValue 2)
          rw [shiftEq] at rightBelow
          exact Nat.lt_irrefl rightValue rightBelow
  | isFalse leftLt =>
      cases Nat.decLe threshold rightValue with
      | isTrue rightGe =>
          exfalso
          rw [freshShiftAbove_ofNotLe threshold 2 leftValue leftLt,
            freshShiftAbove_ofLe threshold 2 rightValue rightGe] at shiftEq
          have leftBelow : leftValue < rightValue + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le leftLt) rightGe)
              (Nat.le_add_right rightValue 2)
          rw [← shiftEq] at leftBelow
          exact Nat.lt_irrefl leftValue leftBelow
      | isFalse rightLt =>
          rw [freshShiftAbove_ofNotLe threshold 2 leftValue leftLt,
            freshShiftAbove_ofNotLe threshold 2 rightValue rightLt] at shiftEq
          exact shiftEq

private theorem mapFreshShiftInjective (threshold : Nat) : (first second : List Nat) →
    first.map (freshShiftAbove threshold 2) = second.map (freshShiftAbove threshold 2) → first = second
  | [], [], _ => rfl
  | [], headSecond :: restSecond, mapEq => by
      have hcons : ([] : List Nat)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := mapEq
      injection hcons
  | headFirst :: restFirst, [], mapEq => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = ([] : List Nat) := mapEq
      injection hcons
  | headFirst :: restFirst, headSecond :: restSecond, mapEq => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := mapEq
      injection hcons with hHead hRest
      rw [freshShiftInjective threshold headFirst headSecond hHead,
        mapFreshShiftInjective threshold restFirst restSecond hRest]

private theorem topCountStepCup (bottomCount : Nat) (state : WireState) (windowPosition : Nat) :
    (extractDiagram bottomCount (stepCup state windowPosition)).topCount
      = (extractDiagram bottomCount state).topCount + 2 :=
  natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]

private theorem extractDiagramPartnerLength (bottomCount : Nat) (state : WireState) :
    (extractDiagram bottomCount state).partner.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

/-! ## The positive-mid reduction to a top-of-stack cup (the tracking hook swapped for the class-generic one) -/

/-- Reduce a pure-cup boundary-chained string spine `prefixAtoms ++ [lastCup]` at width `midWidth` to a top-of-stack
cup fired onto the processed prefix, and supply the prefix state's shipped invariants plus the seed-below-fresh
witness.  The FROZEN FC-3 r45 `stringDropStepReduceMid` proof, generic over the class (the ONLY signature-specific
node — the open-wire tracking — swapped for `genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls`). -/
private theorem genericDropStepReduceMid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (prefixAtoms : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
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
  have domLen := genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls midWidth prefixAtoms lastCup chained
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

/-! ## The drop-injectivity linchpin (downward) -/

/-- ★★ **Dropping a top-of-stack cup is matching-injective at width `midWidth`, over the class (the peel step).**
The FROZEN FC-3 r45 `stringDropLastCup_matching_injective_mid` proof, generic over the class.  Two pure-cup
boundary-chained string spines over the `midWidth` bottom boundary sharing a last cup with equal
`matchingOfSpineList midWidth` have equal-matching prefixes. -/
theorem genericDropLastCup_matching_injective_mid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (firstPrefix secondPrefix : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained midWidth (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained midWidth (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (appendedEqual : matchingOfSpineList midWidth (firstPrefix ++ [lastCup])
      = matchingOfSpineList midWidth (secondPrefix ++ [lastCup])) :
    matchingOfSpineList midWidth firstPrefix = matchingOfSpineList midWidth secondPrefix := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, seedBelowFirst, windowFitsFirst⟩ :=
    genericDropStepReduceMid cls midWidth firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, seedBelowSecond, windowFitsSecond⟩ :=
    genericDropStepReduceMid cls midWidth secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond] at appendedEqual
  show extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)
    = extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)
  have eLoops : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).loops
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).loops := by
    have h := congrArg DiagramType.loops appendedEqual
    exact h
  have eBottom : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).bottomCount
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).bottomCount := rfl
  have eTop : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).topCount
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).topCount := by
    have h := congrArg DiagramType.topCount appendedEqual
    rw [topCountStepCup, topCountStepCup] at h
    exact genericDropNatAddRightCancel 2 _ _ h
  have ePart : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).partner
      = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).partner := by
    have hMapEq : (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)).partner.map
          (freshShiftAbove (midWidth + lastCup.leftContext.length) 2)
        = (extractDiagram midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix)).partner.map
          (freshShiftAbove (midWidth + lastCup.leftContext.length) 2) := by
      apply natListInsertAt_leftInjective (midWidth + lastCup.leftContext.length)
        [midWidth + lastCup.leftContext.length + 1, midWidth + lastCup.leftContext.length] _ _
        (by rw [mapLength, extractDiagramPartnerLength]; exact Nat.add_le_add_left windowFitsFirst midWidth)
        (by rw [mapLength, extractDiagramPartnerLength]; exact Nat.add_le_add_left windowFitsSecond midWidth)
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

/-- A top-of-stack cup congruence at the `extractDiagram` level (`WireState`-only, `{signature}`-blind, re-copied
verbatim from the shipped `stringExtractDiagram_stepCup_congr` — ALREADY seed-general). -/
private theorem genericExtractDiagram_stepCup_congr (seedBoundary : Nat)
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
    rw [topCountStepCup, topCountStepCup]
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

/-- ★★ **The forward matching congruence at width `midWidth`, over the class (the drop's inverse).**  The FROZEN
FC-3 r45 `stringBackAppend_matching_congr_mid` proof, generic over the class.  Two pure-cup boundary-chained
string spines sharing a last cup whose PREFIXES have equal `matchingOfSpineList midWidth` also have equal appended
`matchingOfSpineList midWidth`. -/
theorem genericBackAppend_matching_congr_mid (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (midWidth : Nat)
    (firstPrefix secondPrefix : List (SpineAtom cls.signature overallSource overallTarget))
    (lastCup : SpineAtom cls.signature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained midWidth (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained midWidth (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (prefixEqual : matchingOfSpineList midWidth firstPrefix = matchingOfSpineList midWidth secondPrefix) :
    matchingOfSpineList midWidth (firstPrefix ++ [lastCup])
      = matchingOfSpineList midWidth (secondPrefix ++ [lastCup]) := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, seedBelowFirst, windowFitsFirst⟩ :=
    genericDropStepReduceMid cls midWidth firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, seedBelowSecond, windowFitsSecond⟩ :=
    genericDropStepReduceMid cls midWidth secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond]
  exact genericExtractDiagram_stepCup_congr midWidth (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ firstPrefix)
    (processSpine ⟨List.range midWidth, [], midWidth, 0⟩ secondPrefix) lastCup.leftContext.length
    freshFirst forestFirst freshSecond forestSecond seedBelowFirst seedBelowSecond
    windowFitsFirst prefixEqual

/-! ## `k = 2` RECOVERY — each generic drop brick re-derives the NAMED shipped positive-mid lemma -/

/-- The statement of the shipped `k = 2` drop-injectivity, named as the recovery TARGET. -/
abbrev StringDropInjectiveMidStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat)
    (firstPrefix secondPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    SpineBoundaryChained midWidth (firstPrefix ++ [lastCup]) →
    SpineBoundaryChained midWidth (secondPrefix ++ [lastCup]) →
    AllCupArity (firstPrefix ++ [lastCup]) → AllCupArity (secondPrefix ++ [lastCup]) →
    matchingOfSpineList midWidth (firstPrefix ++ [lastCup])
        = matchingOfSpineList midWidth (secondPrefix ++ [lastCup]) →
    matchingOfSpineList midWidth firstPrefix = matchingOfSpineList midWidth secondPrefix

/-- ★ **The shipped `k = 2` drop-injectivity inhabits the named statement.** -/
theorem stringDropInjectiveMid_shippedInhabitant : StringDropInjectiveMidStatement :=
  @stringDropLastCup_matching_injective_mid

/-- ★★ **The generic drop-injectivity, at `k = 2`, RE-DERIVES the shipped drop-injectivity.** -/
theorem stringDropInjectiveMid_viaGenericClassAtTwo : StringDropInjectiveMidStatement :=
  fun midWidth firstPrefix secondPrefix lastCup chainedFirst chainedSecond pureFirst pureSecond appendedEqual =>
    genericDropLastCup_matching_injective_mid adjointStringConnectivityAtTwo
      midWidth firstPrefix secondPrefix lastCup chainedFirst chainedSecond pureFirst pureSecond appendedEqual

/-- The statement of the shipped `k = 2` back-append congruence, named as the recovery TARGET. -/
abbrev StringBackAppendMidStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (midWidth : Nat)
    (firstPrefix secondPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    SpineBoundaryChained midWidth (firstPrefix ++ [lastCup]) →
    SpineBoundaryChained midWidth (secondPrefix ++ [lastCup]) →
    AllCupArity (firstPrefix ++ [lastCup]) → AllCupArity (secondPrefix ++ [lastCup]) →
    matchingOfSpineList midWidth firstPrefix = matchingOfSpineList midWidth secondPrefix →
    matchingOfSpineList midWidth (firstPrefix ++ [lastCup])
      = matchingOfSpineList midWidth (secondPrefix ++ [lastCup])

/-- ★ **The shipped `k = 2` back-append congruence inhabits the named statement.** -/
theorem stringBackAppendMid_shippedInhabitant : StringBackAppendMidStatement :=
  @stringBackAppend_matching_congr_mid

/-- ★★ **The generic back-append congruence, at `k = 2`, RE-DERIVES the shipped back-append congruence.** -/
theorem stringBackAppendMid_viaGenericClassAtTwo : StringBackAppendMidStatement :=
  fun midWidth firstPrefix secondPrefix lastCup chainedFirst chainedSecond pureFirst pureSecond prefixEqual =>
    genericBackAppend_matching_congr_mid adjointStringConnectivityAtTwo
      midWidth firstPrefix secondPrefix lastCup chainedFirst chainedSecond pureFirst pureSecond prefixEqual

/-! ## `k = 3` FIRES — the generic drop bricks run on genuinely DISTINCT adjoint-quadruple spines

`η1` (`id_base ⇒ L1·L2`) and `η3` (`id_base ⇒ L3·L4`, the fresh letter `L4`) are DISTINCT cup generators with
IDENTICAL arities `(0, 2)`; the two window-`0` prefixes `[η1]` / `[η3]` are distinct spines that the boundary
matching cannot tell apart — the exact shape the drop injectivity discriminates. -/

/-- A `k = 3` window-`0` cup carrying the unit `η1` (`id_base ⇒ L1·L2`). -/
def quadDropUnitOneW0 :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- A `k = 3` window-`0` cup carrying the unit `η3` (`id_base ⇒ L3·L4`, the FRESH letter `L4`) — a DISTINCT
generator from `η1` with the SAME arity. -/
def quadDropUnitThreeW0 :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL3L4
  generator := StringQuadTwoCell.unitThree
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- A `k = 3` shared last cup at window `2` (leftContext `L1·L2`, length `2`). -/
def quadDropLastCupW2 :
    SpineAtom adjointQuadrupleModeSignature AdjointQuadrupleMode.base AdjointQuadrupleMode.base where
  leftMidMode := AdjointQuadrupleMode.base
  rightMidMode := AdjointQuadrupleMode.base
  leftContext := quadL1L2
  generatorDom := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base
  generatorCod := quadL1L2
  generator := StringQuadTwoCell.unitOne
  rightContext := ModalityPath.nil (graph := adjointQuadrupleGraph) AdjointQuadrupleMode.base

/-- The two distinct `k = 3` full spines `[η1, C]` / `[η3, C]` have EQUAL boundary matching `[1, 0, 3, 2]` (the
matching ignores generator identity). -/
theorem quadDropFullFirst_matchingComputes :
    (matchingOfSpineList 0 [quadDropUnitOneW0, quadDropLastCupW2]).partner = [1, 0, 3, 2] := by decide

theorem quadDropFullSecond_matchingComputes :
    (matchingOfSpineList 0 [quadDropUnitThreeW0, quadDropLastCupW2]).partner = [1, 0, 3, 2] := by decide

/-- ★ **The generic drop-injectivity FIRES at `k = 3` on genuinely DISTINCT spines.**  The two window-`0` prefixes
`[η1]` / `[η3]` — DISTINCT cup generators the matching cannot tell apart — share the last cup `C` and have EQUAL
full matchings (`quadDropFull{First,Second}_matchingComputes`, both `[1,0,3,2]`); the generic drop-injectivity at
`adjointStringConnectivityAtThree` cancels `C` and yields equal PREFIX matchings.  The `appendedEqual` hypothesis
is a genuine agreement of two DISTINCT-spine matchings (`by decide`). -/
theorem genericDropInjectiveMid_firesAtThree :
    matchingOfSpineList 0 [quadDropUnitOneW0] = matchingOfSpineList 0 [quadDropUnitThreeW0] :=
  genericDropLastCup_matching_injective_mid adjointStringConnectivityAtThree 0
    [quadDropUnitOneW0] [quadDropUnitThreeW0] quadDropLastCupW2
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (by decide)

/-- ★ **The generic back-append congruence FIRES at `k = 3` on genuinely DISTINCT spines.**  From the equal
window-`0` prefix matchings of `[η1]` / `[η3]` (`by decide`), the generic back-append at
`adjointStringConnectivityAtThree` re-appends the shared last cup `C` and yields equal full matchings. -/
theorem genericBackAppendMid_firesAtThree :
    matchingOfSpineList 0 [quadDropUnitOneW0, quadDropLastCupW2]
      = matchingOfSpineList 0 [quadDropUnitThreeW0, quadDropLastCupW2] :=
  genericBackAppend_matching_congr_mid adjointStringConnectivityAtThree 0
    [quadDropUnitOneW0] [quadDropUnitThreeW0] quadDropLastCupW2
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _)))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (AllCupArity.cons rfl rfl (AllCupArity.cons rfl rfl AllCupArity.nil))
    (by decide)

/-! ## Negative control — dropping is genuinely a cancellation, not a no-op -/

/-- ★ **Negative control: the two DISTINCT prefix spines are not the SAME list.**  `[η1]` and `[η3]` carry
DISTINCT generators (`unitOne` vs `unitThree`), so the drop fire genuinely relates two different spines, not a
diagonal — the boundary matching's blindness to generator identity is exactly what the injection exploits. -/
theorem quadDropPrefixes_distinctGenerators :
    quadDropUnitOneW0.generatorCod ≠ quadDropUnitThreeW0.generatorCod := by
  intro codsEqual
  have indexEq : quadIndexWord quadDropUnitOneW0.generatorCod = quadIndexWord quadDropUnitThreeW0.generatorCod :=
    congrArg quadIndexWord codsEqual
  exact absurd indexEq (by decide)

/-! ## Road marker -/

/-- **★ ESTABLISHED — the generic mid-width DROP-INJECTIVITY tranche is machine-checked (FC-4 r6, the drop tranche
of the generic cup-sort driver).**  The two shipped positive-mid drop bricks re-founded ONCE over
`AdjointStringConnectivity × midWidth`, verbatim modulo the single signature-specific node — the r5 B3 generic
open-wire tracking `genericProcessSpine_prefix_openWires_eq_lastDomBoundary cls`:

  * `genericDropLastCup_matching_injective_mid cls` — the DOWNWARD drop-injectivity linchpin (the peel step);
  * `genericBackAppend_matching_congr_mid cls` — the UPWARD companion (the re-append the locate needs).

The HONESTY LAW discharged: each generic brick recovers the NAMED shipped `k = 2` positive-mid lemma on the nose
(`..._shippedInhabitant` / `..._viaGenericClassAtTwo`, defeq at `adjointStringConnectivityAtTwo`) AND fires at
`k = 3` on genuinely DISTINCT adjoint-quadruple spines — the two window-`0` prefixes `[η1]` / `[η3]` (distinct cup
generators `unitOne` / `unitThree` the matching cannot tell apart, cross-checked full matchings `[1,0,3,2]`) — with
a negative control confirming the two prefixes carry distinct generators (`quadDropPrefixes_distinctGenerators`).

  What this marker does NOT close (THE FLIP LAW): the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false`.  Its bill is the FULL width-`0` quad SORT, which ON TOP of this
  drop tranche + the readoff tranche (`StringGenericMidCupReadoff`) additionally needs, over `cls × midWidth`: the
  generic SNAKE EXCLUSION (the ONE node consuming `0 < midWidth`, riding the positive-boundary involution whose
  generic port re-founds the arc census/perfect-matching tower), the generic fueled LOCATE, the generic fueled SORT
  DRIVER + `GenericPositiveMidPureCupDeterminacy` (recovering `stringPositiveMidPureCupDeterminacy_proof` /
  `stringWidthZeroPureCupDeterminacyShared_proof` at `k = 2`), and the `k = 3` end-to-end SORT decision — the NAMED
  r7 residual.  `= true`. -/
def fxString_hasGenericMidDropInjective : Bool := true

end FX1Poly.Polygraph
