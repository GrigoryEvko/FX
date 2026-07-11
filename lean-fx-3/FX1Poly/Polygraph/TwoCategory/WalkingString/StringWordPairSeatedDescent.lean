import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcPairSeatedDescent
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordBubble
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordLeftMirror
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # WalkingString/StringWordPairSeatedDescent — the WORD-founded prefix descent master at the adjoint triple
(FC-3 r23)

The walking adjunction's prefix bubble descent (`WalkingAdjunction/ArcPrefixBubbleDescent`,
`arcPairSeated_bubblesThroughPrefix`) carries a below-fresh seated cap target to the FRONT of a boundary-chained
prefix, assembling the `BubblesToFront` witness by front-first recursion.  Its two window factorizations
(`adjunctionSpineAtom_contextsFactorLeft_of_disjointWindows` and its mirror) and its emitted carrier are all
pinned by seed LENGTH-RIGIDITY (`adjunctionPath_eq_of_length_eq`), which is FALSE at the adjoint triple
(`stringFG ≠ stringHG` at equal length `2`).  This file re-founds that master on the shared BOUNDARY WORD:

  * `stringArcPairSeated_beforeCapStep_ofSameParities` — ★ the crux prerequisite (the same-parity-GENERIC
    cap-step gap-closing exclusion).  The r22 tip clone `stringArcPairSeated_beforeCapStep_ofTipParities` hardwires
    `tip`; at the triple a cap seats at EITHER parity (`counitLower` at `tip`, `counitUpper` at `base`), so the
    exclusion is re-keyed on a common window MODE `windowMode`: when the seat and the passed cap's window both
    carry `windowMode`, a gap-closing cap at the seat's successor would carry the OPPOSITE mode — refuted by
    `AdjointTripleMode.noConfusion`.

  * `assembleStepRightOfWordPackage` / `assembleStepLeftOfWordPackage` — the two per-step assemblers, ports of
    the arc's `assembleStepRightOfPackage` / `assembleStepLeftOfPackage` with the length-rigid window factorization
    swapped for the WORD factorization (`spineAtom_contextsFactor*_of_disjointWordWindows`, fed the pair's shared
    boundary word) and the carrier swapped for `WordBubblesToFront`.

  * `stringWordPairSeated_bubblesThroughPrefix` — ★ the descent master.  Front-first recursion, STRUCTURAL on the
    prefix list; each step threads BOTH the length boundary chain (the colour-blind seat/freshness bookkeeping,
    reused verbatim) AND the boundary WORD chain (the source of the per-pair factorization).  Cups die on
    freshness (`arcPairSeated_beforeCupStep`, colour-blind); caps die on the same-parity exclusion above, fed the
    passed cap's window mode from the threaded same-window-mode invariant.

## The threaded same-window-mode invariant (the honest deviation from the length-rigid master)

At the single adjunction ALL caps are `tip`, so the arc master derives the passed cap's window parity FREE from
`adjunctionCapAtom_windowPositionMode`.  At the adjoint triple a gap-closing passed cap of the OPPOSITE colour is
geometrically realizable (a `counitUpper` nested between a `counitLower`'s legs is a valid non-crossing valley),
so the exclusion is NOT free from parity alone.  The descent master therefore takes an explicit premise
`prefixSharesWindowMode : ∀ atom ∈ prefixAtoms, atom.leftMidMode = target.leftMidMode` — the honest
"threaded invariant" branch of the recon's open question.  This makes the master TRUE and zero-axiom; discharging
the invariant from the located pure-cap spine (the r20 seat data) is the named r24 residual, not this round.

Raw Lean 4 + Init; structural recursion on the prefix list; the exclusion is one `rw` chain closing on
`AdjointTripleMode.noConfusion`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The crux prerequisite — the same-parity-generic cap-step gap-closing exclusion -/

/-- ★ **Backward descent through a cap at the adjoint triple, same-parity generic.**  When the seat AND the
passed cap's window BOTH carry a common mode `windowMode`, the gap-closing exclusion is free: a cap at the seat's
successor would carry the OPPOSITE mode (`adjointTripleModeAtDistance` on the successor is the opposite),
contradicting its `windowMode` — so a seated pair descends through the cap.  This GENERALIZES the r22 tip clone
`stringArcPairSeated_beforeCapStep_ofTipParities` from the fixed `tip` to ANY common window mode, exactly because
at the triple a cap seats at either parity (`counitLower` at `tip`, `counitUpper` at `base`).  The positional
core `arcPairSeated_beforeCapStep` is reused verbatim (it is colour-blind). -/
theorem stringArcPairSeated_beforeCapStep_ofSameParities (state : ArcWireState)
    (windowPosition : Nat) {leftNode rightNode seatAfter : Nat}
    {sourceMode windowMode : AdjointTripleMode}
    (hasSeatWindowMode :
      adjointTripleModeAtDistance sourceMode seatAfter = windowMode)
    (hasPassedWindowMode :
      adjointTripleModeAtDistance sourceMode windowPosition = windowMode)
    (windowFits : windowPosition + 2 ≤ state.openWires.length)
    (seatedAfter : ArcPairSeated leftNode rightNode seatAfter
      (stepCapArc state windowPosition)) :
    (ArcPairSeated leftNode rightNode seatAfter state ∧ seatAfter + 2 ≤ windowPosition)
      ∨ (ArcPairSeated leftNode rightNode (seatAfter + 2) state
          ∧ windowPosition ≤ seatAfter) := by
  refine arcPairSeated_beforeCapStep state windowPosition ?_ windowFits seatedAfter
  intro isGapClosing
  rw [isGapClosing] at hasPassedWindowMode
  have oppositeIsWindow :
      adjointTripleOppositeMode (adjointTripleModeAtDistance sourceMode seatAfter) = windowMode :=
    hasPassedWindowMode
  rw [hasSeatWindowMode] at oppositeIsWindow
  cases windowMode with
  | base => exact AdjointTripleMode.noConfusion oppositeIsWindow
  | tip => exact AdjointTripleMode.noConfusion oppositeIsWindow

/-! ## Concrete truth-probe — the same-parity exclusion fires on a real cap step -/

/-- A concrete arc-wire state with six open wires `[0,1,2,3,4,5]` (fresh counter at `6`), the anchor for the
same-parity exclusion probe. -/
def stringSameParityProbeState : ArcWireState :=
  ArcWireState.mk [0, 1, 2, 3, 4, 5] [] 6 0 [] []

/-- ★ **The same-parity exclusion fires on a genuine cap step.**  A pair `(2, 3)` seated adjacent at position `0`
AFTER a cap fires at the front window (`stepCapArc … 0`, both seat and window at the `base`-relative distance `0`,
so both carry the same mode) descends to having been seated at position `2` before the cap — the PAST outcome —
run end-to-end through `stringArcPairSeated_beforeCapStep_ofSameParities` on concrete `Nat`/`ArcWireState` data.
A machine-checked non-vacuity witness that the exclusion applies to a real cap, NOT a vacuous statement. -/
theorem stringSameParityProbe_fires :
    (ArcPairSeated 2 3 0 stringSameParityProbeState ∧ 0 + 2 ≤ 0)
      ∨ (ArcPairSeated 2 3 (0 + 2) stringSameParityProbeState ∧ (0 : Nat) ≤ 0) :=
  stringArcPairSeated_beforeCapStep_ofSameParities
    (sourceMode := AdjointTripleMode.base) (windowMode := AdjointTripleMode.base)
    stringSameParityProbeState 0 rfl rfl
    (Nat.le.step (Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl))))
    ⟨rfl, rfl, Nat.le.step (Nat.le.step Nat.le.refl)⟩

/-! ## The two per-step word assemblers (ports of the arc assemblers, length-rigidity swapped for the word factorization) -/

/-- Assemble one `stepRightOf` word-bubble step from the past-window descent outcome: the passed atom's window
sits at-or-before the descended seat, the moved target's window length recomputes through the passed atom's
SOURCE 1-cell plus the minted inert gap path, landing on the descended seat.  Port of the arc's
`assembleStepRightOfPackage` with `adjunctionSpineAtom_contextsFactor_of_disjointWindows` (length-rigid) swapped
for `spineAtom_contextsFactor_of_disjointWordWindows` (fed the pair's shared boundary word) and the carrier
swapped for `WordBubblesToFront`. -/
private theorem assembleStepRightOfWordPackage
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

/-- Assemble one `stepLeftOf` word-bubble step from the below-window descent outcome: the pair sits strictly
below the passed atom's window, the seat is unchanged, and the inert gap path is minted from the LEFT word
factorization.  Port of the arc's `assembleStepLeftOfPackage` with the LEFT length-rigid factorization swapped
for `spineAtom_contextsFactorLeft_of_disjointWordWindows` and the carrier swapped for `WordBubblesToFront`. -/
private theorem assembleStepLeftOfWordPackage
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

/-! ## The descent master -/

/-- ★ **The WORD-founded prefix descent master.**  A cap target whose window seats a below-fresh adjacent pair
at the end of a boundary-chained (length AND word) prefix bubbles to the FRONT: the `WordBubblesToFront`
witness, the preserved cap arities, the pair seated at the moved window in the START state, and the moved
window's parity (its `leftMidMode`, generalized from the arc's fixed `tip`).  Front-first recursion, STRUCTURAL
on the prefix list; each step threads the length chain (colour-blind seat/freshness bookkeeping, reused
verbatim) and the word chain (the source of the per-pair `sharedWord`); cups die on freshness
(`arcPairSeated_beforeCupStep`), caps on the same-parity exclusion
(`stringArcPairSeated_beforeCapStep_ofSameParities`), the passed cap's window mode supplied by the threaded
same-window-mode invariant `prefixSharesWindowMode`.  Re-founds `arcPairSeated_bubblesThroughPrefix` on the
shared boundary word, avoiding its phantom-locked length-rigidity. -/
theorem stringWordPairSeated_bubblesThroughPrefix
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (target : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (hasTargetCapDom : target.generatorDom.length = 2)
    (hasTargetCapCod : target.generatorCod.length = 0)
    (suffixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (leftNode rightNode : Nat) :
    ∀ (prefixAtoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
      (state : ArcWireState)
      (boundaryWord : ModalityPath adjointTripleGraph overallSource overallTarget),
      leftNode < state.nextFresh → rightNode < state.nextFresh →
      SpineBoundaryChained state.openWires.length
        (prefixAtoms ++ target :: suffixAtoms) →
      SpineBoundaryWordChained boundaryWord (prefixAtoms ++ target :: suffixAtoms) →
      ArcPairSeated leftNode rightNode target.leftContext.length
        (processArcSpine state prefixAtoms) →
      (∀ atom, atom ∈ prefixAtoms → atom.leftMidMode = target.leftMidMode) →
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
      intro state _boundaryWord _ _ _ _ seatedEnd _
      exact ⟨target, [], WordBubblesToFront.nil, hasTargetCapDom, hasTargetCapCod, seatedEnd,
        adjointTripleAtom_windowPositionMode target⟩
  | cons passedAtom restPrefix restHypothesis =>
      intro state boundaryWord isLeftFresh isRightFresh chainedRemainder wordChainedRemainder
        seatedEnd prefixSharesWindowMode
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
      obtain ⟨movedTargetOfRest, movedRestPrefix, restWitness, movedDomPin, movedCodPin,
        seatedMid, parityMid⟩ :=
        restHypothesis (stepArcAtom state passedAtom)
          (composePath passedAtom.leftContext
            (composePath passedAtom.generatorCod passedAtom.rightContext))
          (Nat.lt_of_lt_of_le isLeftFresh (stepArcAtom_nextFresh_le state passedAtom))
          (Nat.lt_of_lt_of_le isRightFresh (stepArcAtom_nextFresh_le state passedAtom))
          tailChained tailWordChained seatedEnd
          (fun atom memberProof =>
            prefixSharesWindowMode atom (List.Mem.tail passedAtom memberProof))
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
      cases adjointTripleSpineAtom_hasCupOrCapArity passedAtom with
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
              exact assembleStepLeftOfWordPackage passedAtom restWitness sharedWord
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
              have parityStart : adjointTripleModeAtDistance overallSource seatStart
                  = target.leftMidMode := by
                rw [← seatShiftEq] at parityMid
                exact (adjointTripleModeAtDistance_stableUnderTwoShift overallSource
                  seatStart).symm.trans parityMid
              exact assembleStepRightOfWordPackage passedAtom restWitness sharedWord
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
          have passedWindowMode : adjointTripleModeAtDistance overallSource
              passedAtom.leftContext.length = target.leftMidMode :=
            (adjointTripleAtom_windowPositionMode passedAtom).trans
              (prefixSharesWindowMode passedAtom (List.Mem.head restPrefix))
          cases stringArcPairSeated_beforeCapStep_ofSameParities state
              passedAtom.leftContext.length parityMid passedWindowMode windowFits seatedMid with
          | inl belowOutcome =>
              exact assembleStepLeftOfWordPackage passedAtom restWitness sharedWord
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
              exact assembleStepRightOfWordPackage passedAtom restWitness sharedWord
                movedDomPin movedCodPin windowGap windowGapEq movedSeatSplit seatedStart
                parityStart

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the same-parity-generic cap-step gap-closing exclusion is machine-checked (FC-3 r23, B1).**
`stringArcPairSeated_beforeCapStep_ofSameParities` generalizes the r22 tip clone from the fixed `tip` to ANY
common window mode: when the seat and the passed cap's window carry the same mode `windowMode`, a gap-closing cap
at the seat's successor carries the opposite mode and is refuted by `AdjointTripleMode.noConfusion`.  The
positional core `arcPairSeated_beforeCapStep` is reused verbatim (colour-blind).  `stringSameParityProbe_fires`
fires it end-to-end on a concrete six-wire cap step.  This is the crux prerequisite the word descent master's
cap case rides — the one genuine mathematical dualization the recon flagged, the tip hardwiring lifted to the
two-parity seed.  `= true`. -/
def fxString_hasCapStepSameParityExclusion : Bool := true

/-- **★ ESTABLISHED — the WORD-founded prefix descent master is machine-checked (FC-3 r23, B2).**
`stringWordPairSeated_bubblesThroughPrefix` re-founds the phantom-locked arc master
`arcPairSeated_bubblesThroughPrefix` on the shared BOUNDARY WORD: front-first STRUCTURAL recursion on the prefix
list, each step threading the length chain (colour-blind seat/freshness, reused verbatim) and the word chain
(the per-pair `sharedWord` fed to the WORD window factorizations `spineAtom_contextsFactor*_of_disjointWordWindows`
via `spineBoundaryWordChained_pairSharedWord`), the carrier assembled as `WordBubblesToFront` by the two
assemblers `assembleStepRightOfWordPackage` / `assembleStepLeftOfWordPackage`.  Cups die on freshness
(`arcPairSeated_beforeCupStep`); caps on the same-parity exclusion, the passed cap's window mode supplied by the
threaded invariant.  The moved target keeps its cap arities, seats the pair at its window in the START state, and
its window keeps `target.leftMidMode` parity (generalized from the arc's fixed `tip`).

  THE HONEST DEVIATION (the recon's open question, resolved to the "threaded invariant" branch): the master takes
  an explicit premise `prefixSharesWindowMode : ∀ atom ∈ prefixAtoms, atom.leftMidMode = target.leftMidMode`.  At
  the single adjunction ALL caps are `tip`, so the arc derives the passed cap's window parity FREE; at the adjoint
  triple a gap-closing passed cap of the OPPOSITE colour is geometrically realizable (a `counitUpper` nested
  between a `counitLower`'s legs — a valid non-crossing valley the disjoint-window swap could NOT transpose), so
  the un-threaded master is FALSE and the invariant is genuinely required.  Discharging it from the located
  pure-cap spine's seat data (`StringArcPairCapWindow` / r20) is the named r24 residual, not this round.  The
  import closure avoids the three length-rigidity-locked arc files (`DisjointWindowFactorization`,
  `ArcBubbleToFront`, `ArcPrefixBubbleDescent`).  `= true`. -/
def fxString_hasWordPrefixDescentMaster : Bool := true

end FX1Poly.Polygraph
