import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcOpenEndsDiscipline
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.DisjointWindowFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ArcPrefixBubbleDescent — the seated pair descends the whole prefix, assembling the bubble

The witness-construction master: a cap target seated on a below-fresh adjacent pair at the END
of a boundary-chained prefix bubbles to the FRONT.  The recursion walks the prefix head-first,
mirroring `BubblesToFront`'s own shape: the tail recursion (over the advanced arc state) hands
back the bubbled target with its seat, one `ArcPairSeatedDescent` step carries the seat
backward through the head atom, and the side dichotomy picks the constructor —

  * pair strictly below the head's window → `stepLeftOf`, seat unchanged;
  * head's window at-or-before the seat → `stepRightOf`, seat shifted by the head's
    width change (cup: down two, cap: up two), the moved window length recomputed through
    `composePath_length`.

The bookkeeping threads: freshness through `stepArcAtom_nextFresh_le`, the window-fits bounds
through the chain discipline (`stepArcAtom_openWires_tracksBoundary` keeps
`openWires.length` on the running boundary), tip parity through
`adjunctionModeAtDistance_stableUnderTwoShift` (the seat moves by zero or two), and each
step's inert gap path is minted by the shipped context factorization
(`adjunctionSpineAtom_contextsFactor_of_disjointWindows` and its mirror) from pure `Nat` gap
data.  The gap-closing cap is refuted inside the one-step descent by the tip/base parity
clash — no extra hypothesis surfaces here.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Assemble one `stepLeftOf` bubble step from the below-window descent outcome: the pair sits
strictly below the passed atom's window, the seat is unchanged, and the inert gap path is
minted from the gap between the target's produced window end and the passed window. -/
private theorem assembleStepLeftOfPackage
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target : SpineAtom adjunctionModeSignature overallSource overallTarget}
    (passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    {restPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    {movedTargetOfRest : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {movedRestPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (restWitness : BubblesToFront target restPrefix movedTargetOfRest movedRestPrefix)
    (boundariesChain : movedTargetOfRest.domBoundaryLength = passedAtom.codBoundaryLength)
    (movedDomPin : movedTargetOfRest.generatorDom.length = 2)
    (movedCodPin : movedTargetOfRest.generatorCod.length = 0)
    {leftNode rightNode : Nat} {state : ArcWireState}
    (seatedStart : ArcPairSeated leftNode rightNode movedTargetOfRest.leftContext.length
      state)
    (parityStart : adjunctionModeAtDistance overallSource
        movedTargetOfRest.leftContext.length
      = AdjunctionMode.tip)
    (isPairBelowWindow : movedTargetOfRest.leftContext.length + 2
      ≤ passedAtom.leftContext.length) :
    ∃ (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      BubblesToFront target (passedAtom :: restPrefix) movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 2
        ∧ movedTarget.generatorCod.length = 0
        ∧ ArcPairSeated leftNode rightNode movedTarget.leftContext.length state
        ∧ adjunctionModeAtDistance overallSource movedTarget.leftContext.length
            = AdjunctionMode.tip := by
  obtain ⟨windowGap, windowGapSplit⟩ := Nat.le.dest isPairBelowWindow
  have windowGapEq : movedTargetOfRest.leftContext.length
      + movedTargetOfRest.generatorDom.length + windowGap
      = passedAtom.leftContext.length := by
    rw [movedDomPin]
    exact windowGapSplit
  obtain ⟨inertPath, _, _, inertLength⟩ :=
    adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows passedAtom movedTargetOfRest
      boundariesChain windowGap windowGapEq
  exact ⟨_, _,
    BubblesToFront.stepLeftOf passedAtom restWitness boundariesChain inertPath
      ((congrArg (fun gapLength => movedTargetOfRest.leftContext.length
          + movedTargetOfRest.generatorDom.length + gapLength) inertLength).trans
        windowGapEq),
    movedDomPin, movedCodPin, seatedStart, parityStart⟩

/-- Assemble one `stepRightOf` bubble step from the past-window descent outcome: the passed
atom's window sits at-or-before the seat, the moved target's window length recomputes through
the passed atom's SOURCE 1-cell plus the minted inert gap path, landing on the descended
seat. -/
private theorem assembleStepRightOfPackage
    {overallSource overallTarget : adjunctionGraph.Mode}
    {target : SpineAtom adjunctionModeSignature overallSource overallTarget}
    (passedAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    {restPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    {movedTargetOfRest : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {movedRestPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (restWitness : BubblesToFront target restPrefix movedTargetOfRest movedRestPrefix)
    (boundariesChain : movedTargetOfRest.domBoundaryLength = passedAtom.codBoundaryLength)
    (movedDomPin : movedTargetOfRest.generatorDom.length = 2)
    (movedCodPin : movedTargetOfRest.generatorCod.length = 0)
    {leftNode rightNode seatStart : Nat} {state : ArcWireState} (windowGap : Nat)
    (windowGapEq : passedAtom.leftContext.length + passedAtom.generatorCod.length
        + windowGap
      = movedTargetOfRest.leftContext.length)
    (movedSeatSplit : passedAtom.leftContext.length + passedAtom.generatorDom.length
        + windowGap
      = seatStart)
    (seatedStart : ArcPairSeated leftNode rightNode seatStart state)
    (parityStart : adjunctionModeAtDistance overallSource seatStart = AdjunctionMode.tip) :
    ∃ (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      BubblesToFront target (passedAtom :: restPrefix) movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 2
        ∧ movedTarget.generatorCod.length = 0
        ∧ ArcPairSeated leftNode rightNode movedTarget.leftContext.length state
        ∧ adjunctionModeAtDistance overallSource movedTarget.leftContext.length
            = AdjunctionMode.tip := by
  obtain ⟨inertPath, _, _, inertLength⟩ :=
    adjunctionSpineAtom_contextsFactor_of_disjointWindows passedAtom movedTargetOfRest
      boundariesChain windowGap windowGapEq
  have movedSeatEq : (composePath (composePath passedAtom.leftContext
        passedAtom.generatorDom) inertPath).length = seatStart := by
    rw [composePath_length, composePath_length]
    exact (congrArg (fun gapLength => passedAtom.leftContext.length
        + passedAtom.generatorDom.length + gapLength) inertLength).trans movedSeatSplit
  exact ⟨_, _,
    BubblesToFront.stepRightOf passedAtom restWitness boundariesChain inertPath
      ((congrArg (fun gapLength => passedAtom.leftContext.length
          + passedAtom.generatorCod.length + gapLength) inertLength).trans windowGapEq),
    movedDomPin, movedCodPin, movedSeatEq.symm ▸ seatedStart,
    movedSeatEq.symm ▸ parityStart⟩

/-- ★ **The prefix descent master.**  A cap target whose window seats a below-fresh adjacent
pair at the end of a boundary-chained prefix bubbles to the front: the witness, the preserved
cap arities, the pair seated at the moved window in the START state, and the moved window's
tip parity — everything the head-identification read-off consumes at the canonical seed. -/
theorem arcPairSeated_bubblesThroughPrefix
    {overallSource overallTarget : adjunctionGraph.Mode}
    (target : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasTargetCapDom : target.generatorDom.length = 2)
    (hasTargetCapCod : target.generatorCod.length = 0)
    (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (leftNode rightNode : Nat) :
    ∀ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (state : ArcWireState),
      leftNode < state.nextFresh → rightNode < state.nextFresh →
      SpineBoundaryChained state.openWires.length
        (prefixAtoms ++ target :: suffixAtoms) →
      ArcPairSeated leftNode rightNode target.leftContext.length
        (processArcSpine state prefixAtoms) →
      ∃ (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
        (movedPrefixAtoms :
          List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
        BubblesToFront target prefixAtoms movedTarget movedPrefixAtoms
          ∧ movedTarget.generatorDom.length = 2
          ∧ movedTarget.generatorCod.length = 0
          ∧ ArcPairSeated leftNode rightNode movedTarget.leftContext.length state
          ∧ adjunctionModeAtDistance overallSource movedTarget.leftContext.length
              = AdjunctionMode.tip := by
  intro prefixAtoms
  induction prefixAtoms with
  | nil =>
      intro state _ _ _ seatedEnd
      exact ⟨target, [], BubblesToFront.nil, hasTargetCapDom, hasTargetCapCod, seatedEnd,
        adjunctionCapAtom_windowPositionMode target hasTargetCapDom⟩
  | cons passedAtom restPrefix restHypothesis =>
      intro state isLeftFresh isRightFresh chainedRemainder seatedEnd
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chainedRemainder
      have entryShape : state.openWires.length
          = passedAtom.leftContext.length + passedAtom.generatorDom.length
            + passedAtom.rightContext.length := headFires.symm
      have stepTracks : (stepArcAtom state passedAtom).openWires.length
          = passedAtom.codBoundaryLength :=
        stepArcAtom_openWires_tracksBoundary state passedAtom
          (adjunctionSpineAtom_hasCupOrCapArity passedAtom) headFires.symm
      rw [← stepTracks] at tailChained
      obtain ⟨movedTargetOfRest, movedRestPrefix, restWitness, movedDomPin, movedCodPin,
        seatedMid, parityMid⟩ :=
        restHypothesis (stepArcAtom state passedAtom)
          (Nat.lt_of_lt_of_le isLeftFresh (stepArcAtom_nextFresh_le state passedAtom))
          (Nat.lt_of_lt_of_le isRightFresh (stepArcAtom_nextFresh_le state passedAtom))
          tailChained seatedEnd
      have bubbledChained : SpineBoundaryChained
          (stepArcAtom state passedAtom).openWires.length
          (movedTargetOfRest :: (movedRestPrefix ++ suffixAtoms)) :=
        spineBoundaryChained_of_bubblesToFront restWitness suffixAtoms tailChained
      have boundariesChain : movedTargetOfRest.domBoundaryLength
          = passedAtom.codBoundaryLength :=
        (spineBoundaryChained_tail bubbledChained).1.trans stepTracks
      cases adjunctionSpineAtom_hasCupOrCapArity passedAtom with
      | inl cupArity =>
          obtain ⟨domZero, codTwo⟩ := cupArity
          rw [stepArcAtom_eq_stepCupArc state passedAtom domZero codTwo] at seatedMid
          have windowFits : passedAtom.leftContext.length ≤ state.openWires.length := by
            rw [entryShape]
            exact Nat.le_trans
              (Nat.le_add_right passedAtom.leftContext.length
                passedAtom.generatorDom.length)
              (Nat.le_add_right
                (passedAtom.leftContext.length + passedAtom.generatorDom.length)
                passedAtom.rightContext.length)
          cases arcPairSeated_beforeCupStep state passedAtom.leftContext.length
              isLeftFresh isRightFresh windowFits seatedMid with
          | inl belowOutcome =>
              exact assembleStepLeftOfPackage passedAtom restWitness boundariesChain
                movedDomPin movedCodPin belowOutcome.1 parityMid belowOutcome.2
          | inr pastOutcome =>
              obtain ⟨seatStart, seatShiftEq, seatedStart, isWindowLeSeat⟩ := pastOutcome
              obtain ⟨windowGap, windowGapSplit⟩ := Nat.le.dest isWindowLeSeat
              have windowGapEq : passedAtom.leftContext.length
                  + passedAtom.generatorCod.length + windowGap
                  = movedTargetOfRest.leftContext.length := by
                rw [codTwo,
                  Nat.add_right_comm passedAtom.leftContext.length 2 windowGap,
                  windowGapSplit]
                exact seatShiftEq
              have movedSeatSplit : passedAtom.leftContext.length
                  + passedAtom.generatorDom.length + windowGap = seatStart := by
                rw [domZero, Nat.add_zero]
                exact windowGapSplit
              have parityStart : adjunctionModeAtDistance overallSource seatStart
                  = AdjunctionMode.tip := by
                rw [← seatShiftEq] at parityMid
                exact (adjunctionModeAtDistance_stableUnderTwoShift overallSource
                  seatStart).symm.trans parityMid
              exact assembleStepRightOfPackage passedAtom restWitness boundariesChain
                movedDomPin movedCodPin windowGap windowGapEq movedSeatSplit seatedStart
                parityStart
      | inr capArity =>
          obtain ⟨domTwo, codZero⟩ := capArity
          rw [stepArcAtom_eq_stepCapArc state passedAtom domTwo codZero] at seatedMid
          have windowFits : passedAtom.leftContext.length + 2
              ≤ state.openWires.length := by
            rw [entryShape, domTwo]
            exact Nat.le_add_right (passedAtom.leftContext.length + 2)
              passedAtom.rightContext.length
          cases arcPairSeated_beforeCapStep_ofTipParities state
              passedAtom.leftContext.length parityMid
              (adjunctionCapAtom_windowPositionMode passedAtom domTwo)
              windowFits seatedMid with
          | inl belowOutcome =>
              exact assembleStepLeftOfPackage passedAtom restWitness boundariesChain
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
              have parityStart : adjunctionModeAtDistance overallSource
                  (movedTargetOfRest.leftContext.length + 2) = AdjunctionMode.tip :=
                (adjunctionModeAtDistance_stableUnderTwoShift overallSource
                  movedTargetOfRest.leftContext.length).trans parityMid
              exact assembleStepRightOfPackage passedAtom restWitness boundariesChain
                movedDomPin movedCodPin windowGap windowGapEq movedSeatSplit seatedStart
                parityStart

/-! ## Honesty marker -/

/-- **Honesty marker — the prefix bubble descent is SHIPPED.**  A cap target seated on a
below-fresh adjacent pair at the end of a boundary-chained prefix bubbles to the front: the
`BubblesToFront` witness is CONSTRUCTED by front-first recursion, each step descending the
seat through one arc step (freshness kills cup splices, tip parity kills the gap-closing
cap) and minting its inert gap path from the shipped context factorization.  The moved
target keeps its cap arities, seats the pair at its window in the start state, and its
window keeps tip parity.  NOT yet shipped: the seed read-off (the moved window pinned to the
seed seat position) and the cap-case discharge of SpineArcHeadExtractionChained.  `= true`. -/
def fxMode_hasArcPrefixBubbleDescent : Bool := true

end FX1Poly.Polygraph
