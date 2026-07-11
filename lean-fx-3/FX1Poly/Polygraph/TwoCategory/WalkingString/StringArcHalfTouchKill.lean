import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHalfTouchKill
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcPairLocateTouch
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcComponentPersistence

/-! # WalkingString/StringArcHalfTouchKill — a pinned toucher consumes BOTH tracked nodes, ported
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE substrate)

Colour-blind two-token clone of the walking-adjunction `ArcHalfTouchKill`, re-plumbed onto the FOUR-generator seed.
The located pair-touching cap (`StringArcPairTouchSplit`, Brick 1) cannot HALF-touch: under the final connection pin
and the strand count pin of one, it consumes BOTH tracked nodes.  The only non-generic dependencies are the ported
scan `stringArcPairUntouched_locateTouch` (Brick 1) and the ported persistence
`stringIsSameComponent_processArcSpine_ofBase` (Brick 2a); the union-find / event-pollution kit is `{signature}`-
generic and REUSED by import (the arc file supplies it).

  * ★ `stringArcHalfTouchContradiction` — a one-node touch dies (singleton-component collapse, or two fresh-distinct
    events in one pinned root);
  * ★ `stringArcTouchWindowReadsArePair` — the read-off: the toucher's two window reads are EXACTLY the pair.

Raw Lean 4 + Init; structural recursion only; no `omega` / `simp`-AC / `WellFounded.fix`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

private theorem natNeOfLt {smaller larger : Nat} (strict : smaller < larger) :
    smaller ≠ larger :=
  fun wouldBeEqual => absurd (wouldBeEqual ▸ strict) (Nat.lt_irrefl larger)

/-- ★ **The half-touch kill** (four-generator port): a cap that touches only the OTHER node — while the tracked node
enters it untouched and the final state pins the two nodes connected with exactly one cap event on their strand — is
contradictory.  The three-generator analog of `arcHalfTouchContradiction`. -/
theorem stringArcHalfTouchContradiction
    {sourceMode targetMode : adjointTripleGraph.Mode}
    (splitState : ArcWireState) (windowPosition : Nat)
    (suffixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {node otherNode : Nat}
    (nodesNe : node ≠ otherNode)
    (forestSplit : isUnionFindForest splitState.links)
    (freshPost : ArcStateFresh (stepCapArc splitState windowPosition))
    (forestPost : isUnionFindForest (stepCapArc splitState windowPosition).links)
    (untouchedPost : ArcPairUntouched node node (stepCapArc splitState windowPosition))
    (touchedOther : natListGetAt splitState.openWires windowPosition = otherNode
      ∨ natListGetAt splitState.openWires (windowPosition + 1) = otherNode)
    (pinConnected : isSameComponent
        (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
        node otherNode = true)
    (pinCount : countEventsInRoot
        (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
        (unionFindRootOf
          (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links node)
        (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).capEventNodes
      = 1) :
    False := by
  have firstEventConnected : isSameComponent
      (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
      splitState.nextFresh otherNode = true :=
    stringIsSameComponent_processArcSpine_ofBase suffixAtoms (stepCapArc splitState windowPosition)
      forestPost splitState.nextFresh otherNode
      (isSameComponent_stepCapArc_eventTouchedNode splitState windowPosition forestSplit
        touchedOther)
  have firstEventRecorded : splitState.nextFresh
      ∈ (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).capEventNodes :=
    mem_capEventNodes_processArcSpine suffixAtoms (stepCapArc splitState windowPosition)
      (stepCapArc_newEventMem splitState windowPosition)
  cases stringArcPairUntouched_locateTouch suffixAtoms (stepCapArc splitState windowPosition)
      freshPost untouchedPost with
  | inl survivedToEnd =>
      have otherEqualsNode : otherNode = node :=
        eq_ofSameComponent_ofUnlinked _ survivedToEnd.isLeftUnlinked
          (isSameComponent_ofRootEq _
            (unionFindRootOf_eq_ofSameComponent _ pinConnected).symm)
      exact nodesNe otherEqualsNode.symm
  | inr secondSplit =>
      obtain ⟨secondPrefix, secondToucher, secondSuffix, doesSplitSuffix, _, secondCapDom,
        secondCapCod, secondTouch⟩ := secondSplit
      have expandedTouch :
          natListGetAt (processArcSpine (stepCapArc splitState windowPosition)
              secondPrefix).openWires secondToucher.leftContext.length = node
          ∨ natListGetAt (processArcSpine (stepCapArc splitState windowPosition)
              secondPrefix).openWires secondToucher.leftContext.length = node
          ∨ natListGetAt (processArcSpine (stepCapArc splitState windowPosition)
              secondPrefix).openWires (secondToucher.leftContext.length + 1) = node
          ∨ natListGetAt (processArcSpine (stepCapArc splitState windowPosition)
              secondPrefix).openWires (secondToucher.leftContext.length + 1) = node :=
        secondTouch
      have secondTouchCollapsed :
          natListGetAt (processArcSpine (stepCapArc splitState windowPosition)
              secondPrefix).openWires secondToucher.leftContext.length = node
          ∨ natListGetAt (processArcSpine (stepCapArc splitState windowPosition)
              secondPrefix).openWires (secondToucher.leftContext.length + 1) = node := by
        cases expandedTouch with
        | inl firstHits => exact Or.inl firstHits
        | inr remaining =>
            cases remaining with
            | inl firstHits => exact Or.inl firstHits
            | inr remaining2 =>
                cases remaining2 with
                | inl secondHits => exact Or.inr secondHits
                | inr secondHits => exact Or.inr secondHits
      have forestMid : isUnionFindForest
          (processArcSpine (stepCapArc splitState windowPosition) secondPrefix).links :=
        isUnionFindForest_processArcSpine secondPrefix (stepCapArc splitState windowPosition)
          forestPost
      have capStepEq : stepArcAtom (processArcSpine (stepCapArc splitState windowPosition)
            secondPrefix) secondToucher
          = stepCapArc (processArcSpine (stepCapArc splitState windowPosition) secondPrefix)
              secondToucher.leftContext.length :=
        stepArcAtom_eq_stepCapArc _ secondToucher secondCapDom secondCapCod
      have forestSecondPost : isUnionFindForest
          (stepCapArc (processArcSpine (stepCapArc splitState windowPosition) secondPrefix)
            secondToucher.leftContext.length).links := by
        rw [← capStepEq]
        exact isUnionFindForest_stepArcAtom _ secondToucher forestMid
      have endStateEq : processArcSpine (stepCapArc splitState windowPosition) suffixAtoms
          = processArcSpine
              (stepArcAtom (processArcSpine (stepCapArc splitState windowPosition)
                secondPrefix) secondToucher) secondSuffix := by
        rw [doesSplitSuffix]
        exact processArcSpine_append secondPrefix (secondToucher :: secondSuffix)
          (stepCapArc splitState windowPosition)
      have secondEventRecorded : (processArcSpine (stepCapArc splitState windowPosition)
            secondPrefix).nextFresh
          ∈ (processArcSpine
              (stepCapArc splitState windowPosition) suffixAtoms).capEventNodes := by
        rw [endStateEq, capStepEq]
        exact mem_capEventNodes_processArcSpine secondSuffix _
          (stepCapArc_newEventMem _ secondToucher.leftContext.length)
      have secondEventConnected : isSameComponent
          (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
          (processArcSpine (stepCapArc splitState windowPosition) secondPrefix).nextFresh
          node = true := by
        rw [endStateEq, capStepEq]
        exact stringIsSameComponent_processArcSpine_ofBase secondSuffix _ forestSecondPost _ node
          (isSameComponent_stepCapArc_eventTouchedNode _ secondToucher.leftContext.length
            forestMid secondTouchCollapsed)
      have eventsDistinct : splitState.nextFresh
          ≠ (processArcSpine (stepCapArc splitState windowPosition)
              secondPrefix).nextFresh := by
        have bumpThenMonotone : splitState.nextFresh + 1
            ≤ (processArcSpine (stepCapArc splitState windowPosition)
                secondPrefix).nextFresh := by
          have monotone := processArcSpine_nextFresh_le secondPrefix
            (stepCapArc splitState windowPosition)
          rw [stepCapArc_nextFresh splitState windowPosition] at monotone
          exact monotone
        exact natNeOfLt bumpThenMonotone
      have rootFirst : unionFindRootOf
          (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
          splitState.nextFresh
          = unionFindRootOf
              (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
              node :=
        Eq.trans (unionFindRootOf_eq_ofSameComponent _ firstEventConnected)
          (unionFindRootOf_eq_ofSameComponent _ pinConnected).symm
      have rootSecond : unionFindRootOf
          (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
          (processArcSpine (stepCapArc splitState windowPosition) secondPrefix).nextFresh
          = unionFindRootOf
              (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
              node :=
        unionFindRootOf_eq_ofSameComponent _ secondEventConnected
      have atLeastTwo : 2 ≤ countEventsInRoot
          (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
          (unionFindRootOf
            (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links node)
          (processArcSpine
            (stepCapArc splitState windowPosition) suffixAtoms).capEventNodes :=
        countEventsInRoot_ge_two_ofDistinctMembers
          (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links
          (unionFindRootOf
            (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).links node)
          (processArcSpine (stepCapArc splitState windowPosition) suffixAtoms).capEventNodes
          firstEventRecorded secondEventRecorded eventsDistinct rootFirst rootSecond
      have twoLeOne : 2 ≤ 1 := pinCount ▸ atLeastTwo
      exact absurd twoLeOne (Nat.not_succ_le_self 1)

/-- ★ **The window read-off** (four-generator port): under the connection pin and the left-node count pin, the
located toucher's two window reads are EXACTLY the tracked pair, in one of the two orders.  The three-generator
analog of `arcTouchWindowReadsArePair`. -/
theorem stringArcTouchWindowReadsArePair
    {sourceMode targetMode : adjointTripleGraph.Mode}
    (prefixAtoms suffixAtoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    (toucherAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (state : ArcWireState) {leftIndex rightIndex : Nat}
    (indexesNe : leftIndex ≠ rightIndex)
    (freshSplit : ArcStateFresh (processArcSpine state prefixAtoms))
    (forestSplit : isUnionFindForest (processArcSpine state prefixAtoms).links)
    (untouchedSplit : ArcPairUntouched leftIndex rightIndex
      (processArcSpine state prefixAtoms))
    (hasCapDomArity : toucherAtom.generatorDom.length = 2)
    (hasCapCodArity : toucherAtom.generatorCod.length = 0)
    (doesTouchPair : ArcReadsTouchPair (processArcSpine state prefixAtoms)
      toucherAtom.leftContext.length leftIndex rightIndex)
    (pinConnected : isSameComponent
        (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
          toucherAtom.leftContext.length) suffixAtoms).links leftIndex rightIndex = true)
    (pinCountLeft : countEventsInRoot
        (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
          toucherAtom.leftContext.length) suffixAtoms).links
        (unionFindRootOf
          (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
            toucherAtom.leftContext.length) suffixAtoms).links leftIndex)
        (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
          toucherAtom.leftContext.length) suffixAtoms).capEventNodes
      = 1) :
    (natListGetAt (processArcSpine state prefixAtoms).openWires
        toucherAtom.leftContext.length = leftIndex
      ∧ natListGetAt (processArcSpine state prefixAtoms).openWires
          (toucherAtom.leftContext.length + 1) = rightIndex)
    ∨ (natListGetAt (processArcSpine state prefixAtoms).openWires
        toucherAtom.leftContext.length = rightIndex
      ∧ natListGetAt (processArcSpine state prefixAtoms).openWires
          (toucherAtom.leftContext.length + 1) = leftIndex) := by
  have touchExpanded :
      natListGetAt (processArcSpine state prefixAtoms).openWires
        toucherAtom.leftContext.length = leftIndex
      ∨ natListGetAt (processArcSpine state prefixAtoms).openWires
          toucherAtom.leftContext.length = rightIndex
      ∨ natListGetAt (processArcSpine state prefixAtoms).openWires
          (toucherAtom.leftContext.length + 1) = leftIndex
      ∨ natListGetAt (processArcSpine state prefixAtoms).openWires
          (toucherAtom.leftContext.length + 1) = rightIndex := doesTouchPair
  have capStepEq : stepArcAtom (processArcSpine state prefixAtoms) toucherAtom
      = stepCapArc (processArcSpine state prefixAtoms) toucherAtom.leftContext.length :=
    stepArcAtom_eq_stepCapArc _ toucherAtom hasCapDomArity hasCapCodArity
  have freshPost : ArcStateFresh (stepCapArc (processArcSpine state prefixAtoms)
      toucherAtom.leftContext.length) := by
    rw [← capStepEq]
    exact arcStateFresh_stepArcAtom _ toucherAtom freshSplit
  have forestPost : isUnionFindForest (stepCapArc (processArcSpine state prefixAtoms)
      toucherAtom.leftContext.length).links := by
    rw [← capStepEq]
    exact isUnionFindForest_stepArcAtom _ toucherAtom forestSplit
  have leftMembership : natListGetAt (processArcSpine state prefixAtoms).openWires
      toucherAtom.leftContext.length = leftIndex
      ∨ natListGetAt (processArcSpine state prefixAtoms).openWires
          (toucherAtom.leftContext.length + 1) = leftIndex := by
    cases Nat.decEq (natListGetAt (processArcSpine state prefixAtoms).openWires
        toucherAtom.leftContext.length) leftIndex with
    | isTrue firstHits => exact Or.inl firstHits
    | isFalse firstMisses =>
    cases Nat.decEq (natListGetAt (processArcSpine state prefixAtoms).openWires
        (toucherAtom.leftContext.length + 1)) leftIndex with
    | isTrue secondHits => exact Or.inr secondHits
    | isFalse secondMisses =>
        have touchedRight : natListGetAt (processArcSpine state prefixAtoms).openWires
            toucherAtom.leftContext.length = rightIndex
            ∨ natListGetAt (processArcSpine state prefixAtoms).openWires
                (toucherAtom.leftContext.length + 1) = rightIndex := by
          cases touchExpanded with
          | inl firstLeft => exact absurd firstLeft firstMisses
          | inr remaining =>
              cases remaining with
              | inl firstRight => exact Or.inl firstRight
              | inr remaining2 =>
                  cases remaining2 with
                  | inl secondLeft => exact absurd secondLeft secondMisses
                  | inr secondRight => exact Or.inr secondRight
        have untouchedLeftPost : ArcPairUntouched leftIndex leftIndex
            (stepCapArc (processArcSpine state prefixAtoms)
              toucherAtom.leftContext.length) :=
          arcPairUntouched_stepCapArc_ofDisjointReads _ _ freshSplit
            firstMisses secondMisses firstMisses secondMisses
            ⟨untouchedSplit.isLeftOpen, untouchedSplit.isLeftOpen,
              untouchedSplit.isLeftUnlinked, untouchedSplit.isLeftUnlinked⟩
        exact (stringArcHalfTouchContradiction (processArcSpine state prefixAtoms)
          toucherAtom.leftContext.length suffixAtoms indexesNe forestSplit freshPost
          forestPost untouchedLeftPost touchedRight pinConnected pinCountLeft).elim
  have rootsPinEq : unionFindRootOf
      (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
        toucherAtom.leftContext.length) suffixAtoms).links leftIndex
      = unionFindRootOf
          (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
            toucherAtom.leftContext.length) suffixAtoms).links rightIndex :=
    unionFindRootOf_eq_ofSameComponent _ pinConnected
  have pinConnectedRight : isSameComponent
      (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
        toucherAtom.leftContext.length) suffixAtoms).links rightIndex leftIndex = true :=
    isSameComponent_ofRootEq _ rootsPinEq.symm
  have pinCountRight : countEventsInRoot
      (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
        toucherAtom.leftContext.length) suffixAtoms).links
      (unionFindRootOf
        (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
          toucherAtom.leftContext.length) suffixAtoms).links rightIndex)
      (processArcSpine (stepCapArc (processArcSpine state prefixAtoms)
        toucherAtom.leftContext.length) suffixAtoms).capEventNodes
    = 1 := rootsPinEq ▸ pinCountLeft
  have rightMembership : natListGetAt (processArcSpine state prefixAtoms).openWires
      toucherAtom.leftContext.length = rightIndex
      ∨ natListGetAt (processArcSpine state prefixAtoms).openWires
          (toucherAtom.leftContext.length + 1) = rightIndex := by
    cases Nat.decEq (natListGetAt (processArcSpine state prefixAtoms).openWires
        toucherAtom.leftContext.length) rightIndex with
    | isTrue firstHits => exact Or.inl firstHits
    | isFalse firstMisses =>
    cases Nat.decEq (natListGetAt (processArcSpine state prefixAtoms).openWires
        (toucherAtom.leftContext.length + 1)) rightIndex with
    | isTrue secondHits => exact Or.inr secondHits
    | isFalse secondMisses =>
        have touchedLeft : natListGetAt (processArcSpine state prefixAtoms).openWires
            toucherAtom.leftContext.length = leftIndex
            ∨ natListGetAt (processArcSpine state prefixAtoms).openWires
                (toucherAtom.leftContext.length + 1) = leftIndex := by
          cases touchExpanded with
          | inl firstLeft => exact Or.inl firstLeft
          | inr remaining =>
              cases remaining with
              | inl firstRight => exact absurd firstRight firstMisses
              | inr remaining2 =>
                  cases remaining2 with
                  | inl secondLeft => exact Or.inr secondLeft
                  | inr secondRight => exact absurd secondRight secondMisses
        have untouchedRightPost : ArcPairUntouched rightIndex rightIndex
            (stepCapArc (processArcSpine state prefixAtoms)
              toucherAtom.leftContext.length) :=
          arcPairUntouched_stepCapArc_ofDisjointReads _ _ freshSplit
            firstMisses secondMisses firstMisses secondMisses
            ⟨untouchedSplit.isRightOpen, untouchedSplit.isRightOpen,
              untouchedSplit.isRightUnlinked, untouchedSplit.isRightUnlinked⟩
        exact (stringArcHalfTouchContradiction (processArcSpine state prefixAtoms)
          toucherAtom.leftContext.length suffixAtoms (Ne.symm indexesNe) forestSplit
          freshPost forestPost untouchedRightPost touchedLeft pinConnectedRight
          pinCountRight).elim
  cases leftMembership with
  | inl firstIsLeft =>
      cases rightMembership with
      | inl firstIsRight =>
          exact absurd (firstIsLeft.symm.trans firstIsRight) indexesNe
      | inr secondIsRight => exact Or.inl ⟨firstIsLeft, secondIsRight⟩
  | inr secondIsLeft =>
      cases rightMembership with
      | inl firstIsRight => exact Or.inr ⟨firstIsRight, secondIsLeft⟩
      | inr secondIsRight =>
          exact absurd (secondIsLeft.symm.trans secondIsRight) indexesNe

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the half-touch kill and window read-off ported to the adjoint-triple seed (FC-3 r19).**
`stringArcHalfTouchContradiction` / `stringArcTouchWindowReadsArePair` — colour-blind two-token clones of
`ArcHalfTouchKill`, consuming the ported scan (`stringArcPairUntouched_locateTouch`) and persistence
(`stringIsSameComponent_processArcSpine_ofBase`), with the union-find / event-pollution kit reused generically.
Under the connection pin and the strand count pin of one, the located pair-touching cap consumes BOTH tracked nodes.
`= true`. -/
def fxString_hasArcTouchWindowPinning : Bool := true

end FX1Poly.Polygraph
