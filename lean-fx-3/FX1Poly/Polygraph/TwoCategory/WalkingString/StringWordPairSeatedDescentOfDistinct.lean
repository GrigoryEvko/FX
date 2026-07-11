import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringConsecutiveUntouchedSeat
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDistinctSeatCapExclusion
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWireDistinct
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPairUntouched

/-! # WalkingString/StringWordPairSeatedDescentOfDistinct — the DISTINCTNESS-founded prefix descent master
(FC-3 r25, B2)

The r23 descent master `stringWordPairSeated_bubblesThroughPrefix` took the threaded premise
`prefixSharesWindowMode : ∀ atom ∈ prefixAtoms, atom.leftMidMode = target.leftMidMode`, which the r24 probe
`StringCapWindowColourTruthProbe` showed is FALSE in general.  This file RE-FOUNDS the master on the r24
colour-free exclusion `stringArcPairSeated_beforeCapStep_ofDistinctSeat` in place of that premise, threading the
FORWARD adjacency invariant (B1) instead:

  * The prefix is `AllCapArity` (the located spine is pure-cap), so the CUP arm dies (a cup head contradicts
    `stringHeadCapArity`), and there is no cup to insert BETWEEN the pair — adjacency is preserved forward.
  * Each cap dispatches on its four decidable read-vs-node equalities (the scan's dispatch, `StringArcPairLocateTouch`):
    - **all four MISS** → the cap misses the pair, so distinctness (`stepArcAtom_wireListDistinct`), freshness
      (`arcStateFresh_stepArcAtom`), untouchedness (`arcPairUntouched_stepCapArc_ofDisjointReads`), and adjacency
      (B1 `stringArcPairSeated_stepCapArc_ofDisjointReads`) all push FORWARD to the stepped state, and the
      recursion's descended seat feeds the r24 exclusion (`_ofDistinctSeat`) fed the CURRENT-state adjacency;
    - **any HIT** → the cap consumes a pair node, which then cannot survive to the toucher's located seat
      (`stringMemProcessArcSpine_belowFresh_imp`, B1) while distinctness makes the consumed value gone from the
      removal (`stringNotMem_natListRemoveTwoAt_ofDistinctRead`) — a contradiction with `seatedEnd`.

  * `stringForwardAssembleStepRightOfWordPackage` / `…Left…` — the two per-step word assemblers, re-cloned from
    r23's private assemblers (r17–r24 are byte-intact, so they cannot be reused across the file boundary), used
    unchanged (the exclusion's output dichotomy is byte-identical to r23's `_ofSameParities`).

Raw Lean 4 + Init; structural recursion on the prefix list; the exclusion swap keeps the r23 assembly verbatim.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The removed-value-gone read (positional distinctness) -/

/-- A value read at one of the two removed slots is ABSENT from the two-slot removal, under positional
distinctness: its occurrence is unique, and it sits at the removed slot, so nothing surviving reads it.  A
surviving witness maps back to an original position distinct from both removed slots, contradicting the
injective read-off (`natListGetAt_inj_ofWireListDistinct`). -/
theorem stringNotMem_natListRemoveTwoAt_ofDistinctRead {wires : List Nat}
    (distinct : WireListDistinct wires) {position value : Nat}
    (windowFits : position + 2 ≤ wires.length)
    (readsValue : natListGetAt wires position = value
      ∨ natListGetAt wires (position + 1) = value) :
    value ∉ natListRemoveTwoAt wires position := by
  have removedLength : (natListRemoveTwoAt wires position).length + 2 = wires.length :=
    natListRemoveTwoAt_length wires position windowFits
  have positionBelowLength : position < wires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_of_succ_le (Nat.le_refl (position + 1)))
      (Nat.le_trans (Nat.le_add_right (position + 1) 1) windowFits)
  have positionSuccBelowLength : position + 1 < wires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowFits
  intro memRemoved
  obtain ⟨witnessIndex, witnessBelow, witnessReads⟩ :=
    mem_imp_getAt (natListRemoveTwoAt wires position) memRemoved
  cases Nat.lt_or_ge witnessIndex position with
  | inl belowWindow =>
      have originalRead : natListGetAt wires witnessIndex = value :=
        (natListGetAt_natListRemoveTwoAt_below wires position witnessIndex belowWindow).symm.trans
          witnessReads
      have indexBelowLength : witnessIndex < wires.length :=
        Nat.lt_trans belowWindow positionBelowLength
      cases readsValue with
      | inl readsAtPosition =>
          have indexEqPosition : witnessIndex = position :=
            natListGetAt_inj_ofWireListDistinct distinct indexBelowLength positionBelowLength
              (originalRead.trans readsAtPosition.symm)
          exact absurd indexEqPosition (Nat.ne_of_lt belowWindow)
      | inr readsAtSucc =>
          have indexEqSucc : witnessIndex = position + 1 :=
            natListGetAt_inj_ofWireListDistinct distinct indexBelowLength positionSuccBelowLength
              (originalRead.trans readsAtSucc.symm)
          exact absurd indexEqSucc (Nat.ne_of_lt (Nat.lt_trans belowWindow (Nat.lt_succ_self position)))
  | inr atOrAbove =>
      obtain ⟨gap, gapEq⟩ := Nat.le.dest atOrAbove
      have originalRead : natListGetAt wires (position + gap + 2) = value := by
        have witnessAt : natListGetAt (natListRemoveTwoAt wires position) (position + gap) = value := by
          rw [gapEq]; exact witnessReads
        exact (natListGetAt_natListRemoveTwoAt_pastPair wires position gap windowFits).symm.trans
          witnessAt
      have pastBelowLength : position + gap + 2 < wires.length := by
        have witnessAtRemoved : position + gap < (natListRemoveTwoAt wires position).length := by
          rw [gapEq]; exact witnessBelow
        have shifted : position + gap + 2 < (natListRemoveTwoAt wires position).length + 2 :=
          Nat.add_lt_add_right witnessAtRemoved 2
        rw [removedLength] at shifted
        exact shifted
      have positionLtPast : position < position + gap + 2 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right position gap)
          (Nat.lt_succ_of_le (Nat.le_succ (position + gap)))
      have positionSuccLtPast : position + 1 < position + gap + 2 :=
        Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.le_add_right position gap))
          (Nat.lt_succ_self (position + gap + 1))
      cases readsValue with
      | inl readsAtPosition =>
          have indexEqPosition : position + gap + 2 = position :=
            natListGetAt_inj_ofWireListDistinct distinct pastBelowLength positionBelowLength
              (originalRead.trans readsAtPosition.symm)
          exact absurd indexEqPosition (Nat.ne_of_gt positionLtPast)
      | inr readsAtSucc =>
          have indexEqSucc : position + gap + 2 = position + 1 :=
            natListGetAt_inj_ofWireListDistinct distinct pastBelowLength positionSuccBelowLength
              (originalRead.trans readsAtSucc.symm)
          exact absurd indexEqSucc (Nat.ne_of_gt positionSuccLtPast)

/-! ## The two per-step word assemblers (re-cloned from r23's private assemblers, byte-intact rule) -/

/-- Re-clone of r23's private `assembleStepRightOfWordPackage` (r17–r24 byte-intact, so not reusable across the
file boundary).  Assemble one `stepRightOf` word-bubble step from the past-window descent outcome. -/
private theorem stringForwardAssembleStepRightOfWordPackage
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {target : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    (passedAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    {restPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    {movedTargetOfRest : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    {movedRestPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (restWitness : WordBubblesToFront target restPrefix movedTargetOfRest movedRestPrefix)
    (sharedWord :
      composePath passedAtom.leftContext
          (composePath passedAtom.generatorCod passedAtom.rightContext)
        = composePath movedTargetOfRest.leftContext
            (composePath movedTargetOfRest.generatorDom movedTargetOfRest.rightContext))
    (movedDomPin : movedTargetOfRest.generatorDom.length = 2)
    (movedCodPin : movedTargetOfRest.generatorCod.length = 0)
    {leftNode rightNode seatStart : Nat} {state : ArcWireState} (windowGap : Nat)
    (windowGapEq : passedAtom.leftContext.length + passedAtom.generatorCod.length + windowGap
      = movedTargetOfRest.leftContext.length)
    (movedSeatSplit : passedAtom.leftContext.length + passedAtom.generatorDom.length + windowGap
      = seatStart)
    (seatedStart : ArcPairSeated leftNode rightNode seatStart state)
    (parityStart : adjointTripleModeAtDistance overallSource seatStart = target.leftMidMode) :
    ∃ (movedTarget : SpineAtom adjointTripleModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
      WordBubblesToFront target (passedAtom :: restPrefix) movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 2
        ∧ movedTarget.generatorCod.length = 0
        ∧ ArcPairSeated leftNode rightNode movedTarget.leftContext.length state
        ∧ adjointTripleModeAtDistance overallSource movedTarget.leftContext.length
            = target.leftMidMode := by
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    spineAtom_contextsFactor_of_disjointWordWindows passedAtom movedTargetOfRest sharedWord
      windowGap windowGapEq
  have movedSeatEq : (composePath (composePath passedAtom.leftContext passedAtom.generatorDom)
        inertPath).length = seatStart := by
    rw [composePath_length, composePath_length]
    exact (congrArg (fun gapLength => passedAtom.leftContext.length
        + passedAtom.generatorDom.length + gapLength) inertLength).trans movedSeatSplit
  exact ⟨_, _,
    WordBubblesToFront.stepRightOf passedAtom restWitness inertPath leftFactor rightFactor,
    movedDomPin, movedCodPin, movedSeatEq.symm ▸ seatedStart, movedSeatEq.symm ▸ parityStart⟩

/-- Re-clone of r23's private `assembleStepLeftOfWordPackage`.  Assemble one `stepLeftOf` word-bubble step from
the below-window descent outcome. -/
private theorem stringForwardAssembleStepLeftOfWordPackage
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {target : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    (passedAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    {restPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    {movedTargetOfRest : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    {movedRestPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (restWitness : WordBubblesToFront target restPrefix movedTargetOfRest movedRestPrefix)
    (sharedWord :
      composePath passedAtom.leftContext
          (composePath passedAtom.generatorCod passedAtom.rightContext)
        = composePath movedTargetOfRest.leftContext
            (composePath movedTargetOfRest.generatorDom movedTargetOfRest.rightContext))
    (movedDomPin : movedTargetOfRest.generatorDom.length = 2)
    (movedCodPin : movedTargetOfRest.generatorCod.length = 0)
    {leftNode rightNode : Nat} {state : ArcWireState}
    (seatedStart : ArcPairSeated leftNode rightNode movedTargetOfRest.leftContext.length state)
    (parityStart : adjointTripleModeAtDistance overallSource
        movedTargetOfRest.leftContext.length
      = target.leftMidMode)
    (isPairBelowWindow : movedTargetOfRest.leftContext.length + 2
      ≤ passedAtom.leftContext.length) :
    ∃ (movedTarget : SpineAtom adjointTripleModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
      WordBubblesToFront target (passedAtom :: restPrefix) movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 2
        ∧ movedTarget.generatorCod.length = 0
        ∧ ArcPairSeated leftNode rightNode movedTarget.leftContext.length state
        ∧ adjointTripleModeAtDistance overallSource movedTarget.leftContext.length
            = target.leftMidMode := by
  obtain ⟨windowGap, windowGapSplit⟩ := Nat.le.dest isPairBelowWindow
  have windowGapEq : movedTargetOfRest.leftContext.length
      + movedTargetOfRest.generatorDom.length + windowGap = passedAtom.leftContext.length := by
    rw [movedDomPin]
    exact windowGapSplit
  obtain ⟨inertPath, leftFactor, rightFactor, _⟩ :=
    spineAtom_contextsFactorLeft_of_disjointWordWindows passedAtom movedTargetOfRest sharedWord
      windowGap windowGapEq
  exact ⟨_, _,
    WordBubblesToFront.stepLeftOf passedAtom restWitness inertPath leftFactor rightFactor,
    movedDomPin, movedCodPin, seatedStart, parityStart⟩

/-! ## The touching-cap contradiction (the HIT branch of the dispatch) -/

/-- A read at an in-range position is a member. -/
private theorem stringNatListGetAt_memInRange :
    (wires : List Nat) → (index : Nat) → index < wires.length →
    natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (stringNatListGetAt_memInRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- ★ **A prefix cap that touches the pair contradicts the located seat.**  If a pure-cap prefix cap consumes a
pair node (one of its two reads hits a pair node), that node cannot be open at the toucher's located seat: the
below-fresh membership monotonicity (B1) reflects the seat's open node back to the stepped state, but the
consumed value is gone from the removal under distinctness (`stringNotMem_natListRemoveTwoAt_ofDistinctRead`).
So the HIT branch is impossible, discharging the whole descent conclusion by contradiction. -/
private theorem stringForwardCapHitContradiction
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (target : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (_hasTargetCapDom : target.generatorDom.length = 2)
    (_hasTargetCapCod : target.generatorCod.length = 0)
    (suffixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (passedAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (restPrefix : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (state : ArcWireState) {leftNode rightNode : Nat}
    (fresh : ArcStateFresh state) (distinct : WireListDistinct state.openWires)
    (untouched : ArcPairUntouched leftNode rightNode state)
    (windowFits : passedAtom.leftContext.length + 2 ≤ state.openWires.length)
    (domTwo : passedAtom.generatorDom.length = 2) (codZero : passedAtom.generatorCod.length = 0)
    (seatedEnd : ArcPairSeated leftNode rightNode target.leftContext.length
      (processArcSpine state (passedAtom :: restPrefix)))
    (hit : natListGetAt state.openWires passedAtom.leftContext.length = leftNode
      ∨ natListGetAt state.openWires (passedAtom.leftContext.length + 1) = leftNode
      ∨ natListGetAt state.openWires passedAtom.leftContext.length = rightNode
      ∨ natListGetAt state.openWires (passedAtom.leftContext.length + 1) = rightNode) :
    ∃ (movedTarget : SpineAtom adjointTripleModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
      WordBubblesToFront target (passedAtom :: restPrefix) movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 2
        ∧ movedTarget.generatorCod.length = 0
        ∧ ArcPairSeated leftNode rightNode movedTarget.leftContext.length state
        ∧ adjointTripleModeAtDistance overallSource movedTarget.leftContext.length
            = target.leftMidMode := by
  have stepIsCap : stepArcAtom state passedAtom = stepCapArc state passedAtom.leftContext.length :=
    stepArcAtom_eq_stepCapArc state passedAtom domTwo codZero
  have targetWindowLt : target.leftContext.length
      < (processArcSpine state (passedAtom :: restPrefix)).openWires.length :=
    Nat.lt_of_succ_le (Nat.le_trans (Nat.le_add_right (target.leftContext.length + 1) 1) seatedEnd.2.2)
  have targetWindowSuccLt : target.leftContext.length + 1
      < (processArcSpine state (passedAtom :: restPrefix)).openWires.length :=
    Nat.lt_of_succ_le seatedEnd.2.2
  have leftEndMem : leftNode ∈ (processArcSpine state (passedAtom :: restPrefix)).openWires :=
    seatedEnd.1 ▸ stringNatListGetAt_memInRange _ target.leftContext.length targetWindowLt
  have rightEndMem : rightNode ∈ (processArcSpine state (passedAtom :: restPrefix)).openWires :=
    seatedEnd.2.1 ▸ stringNatListGetAt_memInRange _ (target.leftContext.length + 1) targetWindowSuccLt
  have leftBelowFresh : leftNode < (stepArcAtom state passedAtom).nextFresh :=
    Nat.lt_of_lt_of_le (fresh.1 leftNode untouched.isLeftOpen)
      (stepArcAtom_nextFresh_le state passedAtom)
  have rightBelowFresh : rightNode < (stepArcAtom state passedAtom).nextFresh :=
    Nat.lt_of_lt_of_le (fresh.1 rightNode untouched.isRightOpen)
      (stepArcAtom_nextFresh_le state passedAtom)
  have leftStepped : leftNode ∈ (stepArcAtom state passedAtom).openWires :=
    stringMemProcessArcSpine_belowFresh_imp restPrefix (stepArcAtom state passedAtom) leftBelowFresh
      leftEndMem
  have rightStepped : rightNode ∈ (stepArcAtom state passedAtom).openWires :=
    stringMemProcessArcSpine_belowFresh_imp restPrefix (stepArcAtom state passedAtom) rightBelowFresh
      rightEndMem
  have leftRemoved : leftNode ∈ (stepCapArc state passedAtom.leftContext.length).openWires :=
    stepIsCap ▸ leftStepped
  have rightRemoved : rightNode ∈ (stepCapArc state passedAtom.leftContext.length).openWires :=
    stepIsCap ▸ rightStepped
  cases hit with
  | inl firstHitsLeft =>
      exact absurd leftRemoved
        (stringNotMem_natListRemoveTwoAt_ofDistinctRead distinct windowFits (Or.inl firstHitsLeft))
  | inr hitTail =>
      cases hitTail with
      | inl secondHitsLeft =>
          exact absurd leftRemoved
            (stringNotMem_natListRemoveTwoAt_ofDistinctRead distinct windowFits (Or.inr secondHitsLeft))
      | inr hitRight =>
          cases hitRight with
          | inl firstHitsRight =>
              exact absurd rightRemoved
                (stringNotMem_natListRemoveTwoAt_ofDistinctRead distinct windowFits
                  (Or.inl firstHitsRight))
          | inr secondHitsRight =>
              exact absurd rightRemoved
                (stringNotMem_natListRemoveTwoAt_ofDistinctRead distinct windowFits
                  (Or.inr secondHitsRight))

/-! ## The distinctness-founded descent master -/

/-- ★ **The DISTINCTNESS-founded prefix descent master.**  Re-founds r23's
`stringWordPairSeated_bubblesThroughPrefix` on the r24 colour-free exclusion
`stringArcPairSeated_beforeCapStep_ofDistinctSeat`, dropping the false `prefixSharesWindowMode` premise and
threading instead the FORWARD adjacency invariant (B1) plus positional distinctness / freshness / untouchedness.
The prefix is `AllCapArity` (so cups — the only atom that could split the pair — never appear); each cap
dispatches four-ways on its reads, MISSes push the invariants forward and feed the exclusion the current-state
adjacency, and a HIT contradicts the located seat (`stringMemProcessArcSpine_belowFresh_imp` +
`stringNotMem_natListRemoveTwoAt_ofDistinctRead`).  The `WordBubblesToFront` assembly is byte-identical to r23's
(the exclusion output dichotomy matches `_ofSameParities`). -/
theorem stringWordPairSeated_bubblesThroughPrefix_ofDistinct
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (target : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (hasTargetCapDom : target.generatorDom.length = 2)
    (hasTargetCapCod : target.generatorCod.length = 0)
    (suffixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (leftNode rightNode : Nat) :
    ∀ (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
      (state : ArcWireState)
      (boundaryWord : ModalityPath adjointTripleGraph overallSource overallTarget),
      ArcStateFresh state →
      WireListDistinct state.openWires →
      ArcPairUntouched leftNode rightNode state →
      (∃ seatBefore, ArcPairSeated leftNode rightNode seatBefore state) →
      AllCapArity prefixAtoms →
      SpineBoundaryChained state.openWires.length
        (prefixAtoms ++ target :: suffixAtoms) →
      SpineBoundaryWordChained boundaryWord (prefixAtoms ++ target :: suffixAtoms) →
      ArcPairSeated leftNode rightNode target.leftContext.length
        (processArcSpine state prefixAtoms) →
      ∃ (movedTarget : SpineAtom adjointTripleModeSignature overallSource overallTarget)
        (movedPrefixAtoms :
          List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
        WordBubblesToFront target prefixAtoms movedTarget movedPrefixAtoms
          ∧ movedTarget.generatorDom.length = 2
          ∧ movedTarget.generatorCod.length = 0
          ∧ ArcPairSeated leftNode rightNode movedTarget.leftContext.length state
          ∧ adjointTripleModeAtDistance overallSource movedTarget.leftContext.length
              = target.leftMidMode := by
  intro prefixAtoms
  induction prefixAtoms with
  | nil =>
      intro state _boundaryWord _fresh _distinct _untouched _seatedBefore _allCap _ _ seatedEnd
      exact ⟨target, [], WordBubblesToFront.nil, hasTargetCapDom, hasTargetCapCod, seatedEnd,
        adjointTripleAtom_windowPositionMode target⟩
  | cons passedAtom restPrefix restHypothesis =>
      intro state boundaryWord fresh distinct untouched seatedBefore allCapPrefix chainedRemainder
        wordChainedRemainder seatedEnd
      obtain ⟨domTwo, codZero⟩ := stringHeadCapArity allCapPrefix
      have allCapRest : AllCapArity restPrefix := stringAllCapArity_ofCons allCapPrefix
      obtain ⟨seatBefore, seatedBeforeInState⟩ := seatedBefore
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chainedRemainder
      obtain ⟨headWordFires, tailWordChained⟩ :=
        spineBoundaryWordChained_tail wordChainedRemainder
      have entryShape : state.openWires.length
          = passedAtom.leftContext.length + passedAtom.generatorDom.length
            + passedAtom.rightContext.length := headFires.symm
      have stepTracks : (stepArcAtom state passedAtom).openWires.length
          = passedAtom.codBoundaryLength :=
        stepArcAtom_openWires_tracksBoundary state passedAtom
          (adjointTripleSpineAtom_hasCupOrCapArity passedAtom) headFires.symm
      rw [← stepTracks] at tailChained
      have windowFits : passedAtom.leftContext.length + 2
          ≤ state.openWires.length := by
        rw [entryShape, domTwo]
        exact Nat.le_add_right (passedAtom.leftContext.length + 2)
          passedAtom.rightContext.length
      -- Dispatch on the passed cap's four reads (the scan's dispatch): all misses push the invariant forward,
      -- any hit contradicts the located seat.
      cases Nat.decEq (natListGetAt state.openWires passedAtom.leftContext.length) leftNode with
      | isTrue firstHitsLeft =>
          exact stringForwardCapHitContradiction target hasTargetCapDom hasTargetCapCod suffixAtoms
            passedAtom restPrefix state fresh distinct untouched windowFits domTwo codZero
            seatedEnd (Or.inl firstHitsLeft)
      | isFalse firstMissesLeft =>
      cases Nat.decEq (natListGetAt state.openWires passedAtom.leftContext.length) rightNode with
      | isTrue firstHitsRight =>
          exact stringForwardCapHitContradiction target hasTargetCapDom hasTargetCapCod suffixAtoms
            passedAtom restPrefix state fresh distinct untouched windowFits domTwo codZero
            seatedEnd (Or.inr (Or.inr (Or.inl firstHitsRight)))
      | isFalse firstMissesRight =>
      cases Nat.decEq (natListGetAt state.openWires (passedAtom.leftContext.length + 1)) leftNode with
      | isTrue secondHitsLeft =>
          exact stringForwardCapHitContradiction target hasTargetCapDom hasTargetCapCod suffixAtoms
            passedAtom restPrefix state fresh distinct untouched windowFits domTwo codZero
            seatedEnd (Or.inr (Or.inl secondHitsLeft))
      | isFalse secondMissesLeft =>
      cases Nat.decEq (natListGetAt state.openWires (passedAtom.leftContext.length + 1)) rightNode with
      | isTrue secondHitsRight =>
          exact stringForwardCapHitContradiction target hasTargetCapDom hasTargetCapCod suffixAtoms
            passedAtom restPrefix state fresh distinct untouched windowFits domTwo codZero
            seatedEnd (Or.inr (Or.inr (Or.inr secondHitsRight)))
      | isFalse secondMissesRight =>
          -- All four miss: push the invariants forward and recurse.
          have stepIsCap :
              stepArcAtom state passedAtom = stepCapArc state passedAtom.leftContext.length :=
            stepArcAtom_eq_stepCapArc state passedAtom domTwo codZero
          have distinctNext : WireListDistinct (stepArcAtom state passedAtom).openWires :=
            stepArcAtom_wireListDistinct state passedAtom fresh distinct
          have freshNext : ArcStateFresh (stepArcAtom state passedAtom) :=
            arcStateFresh_stepArcAtom state passedAtom fresh
          have untouchedNext :
              ArcPairUntouched leftNode rightNode (stepArcAtom state passedAtom) := by
            rw [stepIsCap]
            exact arcPairUntouched_stepCapArc_ofDisjointReads state passedAtom.leftContext.length fresh
              firstMissesLeft secondMissesLeft firstMissesRight secondMissesRight untouched
          have seatedNext : ∃ nextSeat,
              ArcPairSeated leftNode rightNode nextSeat (stepArcAtom state passedAtom) := by
            rw [stepIsCap]
            exact stringArcPairSeated_stepCapArc_ofDisjointReads state passedAtom.leftContext.length
              seatedBeforeInState windowFits firstMissesLeft secondMissesLeft firstMissesRight
              secondMissesRight
          obtain ⟨movedTargetOfRest, movedRestPrefix, restWitness, movedDomPin, movedCodPin,
            seatedMid, parityMid⟩ :=
            restHypothesis (stepArcAtom state passedAtom)
              (composePath passedAtom.leftContext
                (composePath passedAtom.generatorCod passedAtom.rightContext))
              freshNext distinctNext untouchedNext seatedNext allCapRest tailChained tailWordChained
              seatedEnd
          have bubbledWordChained : SpineBoundaryWordChained
              (composePath passedAtom.leftContext
                (composePath passedAtom.generatorCod passedAtom.rightContext))
              (movedTargetOfRest :: (movedRestPrefix ++ suffixAtoms)) :=
            spineBoundaryWordChained_of_wordBubblesToFront restWitness suffixAtoms tailWordChained
          have sharedWord : composePath passedAtom.leftContext
                (composePath passedAtom.generatorCod passedAtom.rightContext)
              = composePath movedTargetOfRest.leftContext
                  (composePath movedTargetOfRest.generatorDom movedTargetOfRest.rightContext) :=
            spineBoundaryWordChained_pairSharedWord
              (SpineBoundaryWordChained.cons passedAtom headWordFires bubbledWordChained)
          rw [stepIsCap] at seatedMid
          cases stringArcPairSeated_beforeCapStep_ofDistinctSeat state passedAtom.leftContext.length
              distinct seatedBeforeInState windowFits seatedMid with
          | inl belowOutcome =>
              exact stringForwardAssembleStepLeftOfWordPackage passedAtom restWitness sharedWord
                movedDomPin movedCodPin belowOutcome.1 parityMid belowOutcome.2
          | inr pastOutcome =>
              obtain ⟨seatedStart, isWindowLeSeat⟩ := pastOutcome
              obtain ⟨windowGap, windowGapSplit⟩ := Nat.le.dest isWindowLeSeat
              have windowGapEq : passedAtom.leftContext.length
                  + passedAtom.generatorCod.length + windowGap
                  = movedTargetOfRest.leftContext.length := by
                rw [codZero, Nat.add_zero]
                exact windowGapSplit
              have movedSeatSplit : passedAtom.leftContext.length
                  + passedAtom.generatorDom.length + windowGap
                  = movedTargetOfRest.leftContext.length + 2 := by
                rw [domTwo,
                  Nat.add_right_comm passedAtom.leftContext.length 2 windowGap,
                  windowGapSplit]
              have parityStart : adjointTripleModeAtDistance overallSource
                  (movedTargetOfRest.leftContext.length + 2) = target.leftMidMode :=
                (adjointTripleModeAtDistance_stableUnderTwoShift overallSource
                  movedTargetOfRest.leftContext.length).trans parityMid
              exact stringForwardAssembleStepRightOfWordPackage passedAtom restWitness sharedWord
                movedDomPin movedCodPin windowGap windowGapEq movedSeatSplit seatedStart
                parityStart

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the DISTINCTNESS-founded prefix descent master is machine-checked (FC-3 r25, B2).**
`stringWordPairSeated_bubblesThroughPrefix_ofDistinct` re-founds r23's descent on the r24 colour-free exclusion,
dropping the FALSE `prefixSharesWindowMode` premise: the `AllCapArity` prefix has no cups (so nothing splits the
pair), each cap dispatches four-ways, MISSes push the FORWARD adjacency invariant (B1) plus
distinctness/freshness/untouchedness to the stepped state and feed the r24 exclusion the current-state adjacency,
and any HIT contradicts the located seat via the below-fresh membership monotonicity (B1) and the removed-value
read.  The `WordBubblesToFront` assembly is byte-identical to r23.  NOT yet shipped this brick: the pin-prime
four-conjunct assembly (B3).  `= true`. -/
def fxString_hasWordPairSeatedDescentOfDistinct : Bool := true

end FX1Poly.Polygraph
