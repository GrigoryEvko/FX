import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellWindowSegmentRun

/-! # MODE-COMMUTE r28 — `atomPastCell`: one turnback atom commutes past a WHOLE multi-atom cell

## What this ships (Brick 2 of the whole-cell fold)

The r27 residual's first genuinely multi-atom layer: a single cap (resp. cup) fired below the
window commutes past an ENTIRE turnback-only cell run inside the window — both firing orders are
related by a full eight-field `ArcStepSimCount` whose carrier is a composite of the r25/r27
pairwise block rotations, packaged with the `ArcBoundedSwapCarrier` bounds (injective, fixes
below the initial fresh frontier, fixes at-or-above the final one) that make composites and
common-suffix extensions type-check without re-deriving side conditions.

The induction over the cell:

  * `.gen` — the four r25/r27 general pairwise arms (`arcDisjointCapCapSwapSimCount_ofWellFormed`
    at the sharp three-disequality guard read off the segment invariant,
    `arcDisjointCapCupSwapSimCount_ofWellFormed`, `arcDisjointCupCapSwapSimCount_ofWellFormed`,
    `twoCupGodement_arcStepSimCount`), positions produced by the whisker-length bookkeeping;
  * `.vcomp` — THE CRUX, discharged: swap past the first factor (IH), extend by the second factor
    as a common suffix (`arcStepSimCount_runArcCell_ofWellFormed` + the carrier bounds), then swap
    past the second factor from the intermediate state (IH), whose window decomposition AND
    component guard are re-established by the r28 segment-run engine
    (`arcCellSegmentRun_ofWellFormed` — the fold invariant transported through the first factor);
    the two simulations chain by `arcStepSimCount_comp` along the composed carrier;
  * whiskers — decomposition re-association, the untouched flank riding the general transport.

The cap theorem carries the component guard (the r26 machine-forced doctrine: WINDOW-disjointness
is insufficient; the guard is component-level); the cup theorem is UNGUARDED (fresh legs).

## Honesty

This is `atomPastCell`, NOT `cellPastCell`: the atom side is a single cap/cup.  The whole-cell
pins stay `false`.  Brick 3 (`ArcCellPastCellSwapSimCount`) closes the second induction.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` + independent
`#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The bounded swap carrier — the sigma-bundle the fold composes -/

/-- The bounds every swap carrier in the fold satisfies: injective, the identity below the
initial fresh frontier (hence on the boundary and on `0`), and the identity at-or-above the
final fresh frontier (hence extendable by common suffixes).  Every pairwise block rotation
satisfies it and it is closed under composition — the whole-cell sigma is a composite of these. -/
structure ArcBoundedSwapCarrier (initialFresh finalFresh : Nat) (sigma : Nat → Nat) : Prop where
  /-- The carrier is injective. -/
  isInjective : ∀ firstNode secondNode, sigma firstNode = sigma secondNode → firstNode = secondNode
  /-- The carrier fixes every id below the initial fresh frontier. -/
  fixesBelowInitial : ∀ node, node < initialFresh → sigma node = node
  /-- The carrier fixes every id at-or-above the final fresh frontier. -/
  fixesAboveFinal : ∀ node, finalFresh ≤ node → sigma node = node

/-- The identity carrier is bounded at any window. -/
theorem arcBoundedSwapCarrier_identity (initialFresh finalFresh : Nat) :
    ArcBoundedSwapCarrier initialFresh finalFresh (fun node => node) :=
  ⟨fun _ _ imagesEqual => imagesEqual, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Bounds weaken monotonically: lower the initial frontier, raise the final one. -/
theorem arcBoundedSwapCarrier_weaken {initialFresh finalFresh : Nat} {sigma : Nat → Nat}
    (carrier : ArcBoundedSwapCarrier initialFresh finalFresh sigma)
    {newInitial newFinal : Nat} (initialLe : newInitial ≤ initialFresh)
    (finalLe : finalFresh ≤ newFinal) :
    ArcBoundedSwapCarrier newInitial newFinal sigma :=
  ⟨carrier.isInjective,
   fun node nodeBelow => carrier.fixesBelowInitial node (Nat.lt_of_lt_of_le nodeBelow initialLe),
   fun node nodeAtLeast => carrier.fixesAboveFinal node (Nat.le_trans finalLe nodeAtLeast)⟩

/-- Bounded carriers compose (same window). -/
theorem arcBoundedSwapCarrier_comp {initialFresh finalFresh : Nat}
    {sigmaFirst sigmaSecond : Nat → Nat}
    (carrierFirst : ArcBoundedSwapCarrier initialFresh finalFresh sigmaFirst)
    (carrierSecond : ArcBoundedSwapCarrier initialFresh finalFresh sigmaSecond) :
    ArcBoundedSwapCarrier initialFresh finalFresh (fun node => sigmaSecond (sigmaFirst node)) :=
  ⟨fun firstNode secondNode imagesEqual =>
      carrierFirst.isInjective firstNode secondNode
        (carrierSecond.isInjective _ _ imagesEqual),
   fun node nodeBelow => by
      rw [carrierFirst.fixesBelowInitial node nodeBelow]
      exact carrierSecond.fixesBelowInitial node nodeBelow,
   fun node nodeAtLeast => by
      rw [carrierFirst.fixesAboveFinal node nodeAtLeast]
      exact carrierSecond.fixesAboveFinal node nodeAtLeast⟩

/-- A block rotation whose window sits inside `[initialFresh, finalFresh)` is a bounded carrier. -/
theorem arcBoundedSwapCarrier_blockRotate (baseFresh widthFirst widthSecond : Nat)
    {initialFresh finalFresh : Nat} (initialLe : initialFresh ≤ baseFresh)
    (windowLe : baseFresh + widthFirst + widthSecond ≤ finalFresh) :
    ArcBoundedSwapCarrier initialFresh finalFresh (blockRotate baseFresh widthFirst widthSecond) :=
  ⟨blockRotate_inj baseFresh widthFirst widthSecond,
   fun node nodeBelow => blockRotate_fixesBelow baseFresh widthFirst widthSecond node
     (Nat.lt_of_lt_of_le nodeBelow initialLe),
   fun node nodeAtLeast => blockRotate_fixesAbove baseFresh widthFirst widthSecond node
     (Nat.le_trans windowLe nodeAtLeast)⟩

/-- ★ **Common-suffix extension.**  A bounded-carrier simulation extends through a shared cell run
on both sides — the carrier's `fixesAboveFinal` IS the `fixesAbove` side condition of the shipped
r24 bundle-threaded extension, and the final frontier rides up monotonically. -/
theorem arcStepSimCount_extendByCommonCell {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (initialFresh : Nat) (initialPositive : 0 < initialFresh)
    (stateRedex stateReduct : ArcWireState)
    (wellFormedRedex : WellFormedArcState stateRedex)
    (wellFormedReduct : WellFormedArcState stateReduct)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (carrier : ArcBoundedSwapCarrier initialFresh stateRedex.nextFresh sigma)
    (simulation : ArcStepSimCount sigma stateRedex stateReduct) :
    ArcStepSimCount sigma (runArcCell stateRedex leftAcc rightAcc cell)
        (runArcCell stateReduct leftAcc rightAcc cell)
      ∧ ArcBoundedSwapCarrier initialFresh
          (runArcCell stateRedex leftAcc rightAcc cell).nextFresh sigma :=
  ⟨arcStepSimCount_runArcCell_ofWellFormed sigma carrier.isInjective
      (carrier.fixesBelowInitial 0 initialPositive) stateRedex stateReduct wellFormedRedex
      wellFormedReduct leftAcc rightAcc cell carrier.fixesAboveFinal simulation,
   arcBoundedSwapCarrier_weaken carrier (Nat.le_refl _)
     (runArcCell_nextFresh_le stateRedex leftAcc rightAcc cell)⟩

/-! ## A read-membership brick -/

/-- An in-range read is a member of the wire list. -/
theorem natListGetAt_memOfBelow : (wires : List Nat) → (position : Nat) →
    position < wires.length → natListGetAt wires position ∈ wires
  | [], position, isBelow => absurd isBelow (Nat.not_lt_zero position)
  | _ :: restWires, 0, _ => List.Mem.head restWires
  | headWire :: restWires, position + 1, isBelow =>
      List.Mem.tail headWire
        (natListGetAt_memOfBelow restWires position (Nat.lt_of_succ_lt_succ isBelow))

/-! ## `atomPastCell`, cap side (guarded) -/

/-- ★★ **A CAP commutes past a WHOLE turnback-only cell** (the r27-named `atomPastCell`, cap
side).  The cap fires at `capPosition` inside the prefix (`capPosition + 2 <= |prefix|`); the
cell runs inside the window right of the prefix (`|betaLeftMid| = |prefix|` before the cap,
`|betaLeftHigh| = |prefix| - 2` after it).  Under the component guard — the cap's two reads are
component-disjoint from EVERY window wire — the two orders are `ArcStepSimCount`-related by a
bounded composite carrier.  The guard is re-established at every intermediate state by the r28
segment-run engine; the r26 counterexample shows it cannot be dropped. -/
theorem arcCapAtomPastCellSwapSimCount {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {betaLocalSource betaLocalTarget : signature.graph.Mode} →
    {betaDom betaCod : ModalityPath signature.graph betaLocalSource betaLocalTarget} →
    (cellBeta : RawTwoCellExpr signature betaDom betaCod) →
    (betaLeftHigh betaLeftMid : ModalityPath signature.graph overallSource betaLocalSource) →
    (betaRight : ModalityPath signature.graph betaLocalTarget overallTarget) →
    (state : ArcWireState) → (prefixWires domSegment suffixWires : List Nat) →
    (capPosition : Nat) →
    WellFormedArcState state →
    cellBeta.isTurnbackOnly = true →
    state.openWires = prefixWires ++ (domSegment ++ suffixWires) →
    prefixWires.length = betaLeftMid.length →
    betaLeftHigh.length + 2 = betaLeftMid.length →
    domSegment.length = betaDom.length →
    capPosition + 2 ≤ prefixWires.length →
    arcProbeDisjointFromSegment state.links (natListGetAt state.openWires capPosition)
      domSegment →
    arcProbeDisjointFromSegment state.links (natListGetAt state.openWires (capPosition + 1))
      domSegment →
    ∃ sigma,
      ArcBoundedSwapCarrier state.nextFresh
          (runArcCell (stepCapArc state capPosition) betaLeftHigh betaRight cellBeta).nextFresh
          sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (stepCapArc state capPosition) betaLeftHigh betaRight cellBeta)
            (stepCapArc (runArcCell state betaLeftMid betaRight cellBeta) capPosition)
  | _, _, _, _, .id _, betaLeftHigh, betaLeftMid, betaRight, state, prefixWires, domSegment,
      suffixWires, capPosition, wellFormed, _, _, _, _, _, _, _, _ =>
    ⟨fun node => node,
     arcBoundedSwapCarrier_identity state.nextFresh (stepCapArc state capPosition).nextFresh,
     arcStepSimCount_refl (stepCapArc state capPosition)
       (isUnionFindForest_stepCapArc state capPosition wellFormed.isForest)⟩
  | _, _, betaDom, betaCod, .gen genBeta, betaLeftHigh, betaLeftMid, betaRight, state,
      prefixWires, domSegment, suffixWires, capPosition, wellFormed, isTurnback, decomp,
      prefixLen, highLen, segLen, capWindow, guardLeftHyp, guardRightHyp => by
    obtain ⟨gapVal, gapEq⟩ : ∃ gapValue, gapValue + (capPosition + 2) = prefixWires.length :=
      ⟨prefixWires.length - (capPosition + 2),
        subAddCancel (capPosition + 2) prefixWires.length capWindow⟩
    have prefixAsArmA : prefixWires.length = gapVal + 2 + capPosition := by
      rw [← gapEq, Nat.add_comm capPosition 2, ← Nat.add_assoc]
    have prefixAsArmB : prefixWires.length = gapVal + capPosition + 2 := by
      rw [prefixAsArmA, Nat.add_right_comm gapVal 2 capPosition]
    have midAsArm : betaLeftMid.length = gapVal + 2 + capPosition :=
      prefixLen.symm.trans prefixAsArmA
    have highAsArm : betaLeftHigh.length = gapVal + capPosition :=
      natAddRightCancelSeg betaLeftHigh.length (gapVal + capPosition) 2
        ((highLen.trans prefixLen.symm).trans prefixAsArmB)
    have openLen : state.openWires.length
        = prefixWires.length + (domSegment ++ suffixWires).length := by
      rw [decomp]
      exact lengthAppend prefixWires (domSegment ++ suffixWires)
    cases boolEitherTrueOfOrTrue isTurnback with
    | inr isCap =>
        obtain ⟨domTwoBeq, codZeroBeq⟩ := boolBothTrueOfAndTrue isCap
        have domTwo : betaDom.length = 2 := of_decide_eq_true domTwoBeq
        have codZero : betaCod.length = 0 := of_decide_eq_true codZeroBeq
        obtain ⟨readLeftWire, readRightWire, segPair⟩ :=
          natListEqPairOfLengthTwo domSegment (segLen.trans domTwo)
        subst segPair
        have readHighFirst : natListGetAt state.openWires (gapVal + 2 + capPosition)
            = readLeftWire := by
          rw [← prefixAsArmA, decomp]
          show natListGetAt (prefixWires ++ ([readLeftWire, readRightWire] ++ suffixWires))
              (prefixWires.length + 0) = readLeftWire
          exact natListGetAt_appendAtLength prefixWires
            ([readLeftWire, readRightWire] ++ suffixWires) 0
        have readHighSecond : natListGetAt state.openWires (gapVal + 2 + capPosition + 1)
            = readRightWire := by
          rw [← prefixAsArmA, decomp]
          exact natListGetAt_appendAtLength prefixWires
            ([readLeftWire, readRightWire] ++ suffixWires) 1
        have armInstance := arcDisjointCapCapSwapSimCount_ofWellFormed state capPosition gapVal
          wellFormed
          (Nat.le_trans capWindow (by rw [openLen]; exact Nat.le_add_right _ _))
          (by rw [readHighFirst]; exact guardLeftHyp readLeftWire (List.Mem.head _))
          (by rw [readHighSecond];
              exact guardLeftHyp readRightWire (List.Mem.tail _ (List.Mem.head _)))
          (by rw [readHighFirst]; exact guardRightHyp readLeftWire (List.Mem.head _))
        have redexRuns : runArcCell (stepCapArc state capPosition) betaLeftHigh betaRight
            (RawTwoCellExpr.gen genBeta)
            = stepCapArc (stepCapArc state capPosition) (gapVal + capPosition) := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCapArc (stepCapArc state capPosition)
            (SpineAtom.mk _ _ betaLeftHigh betaDom betaCod genBeta betaRight) domTwo codZero]
          show stepCapArc (stepCapArc state capPosition) betaLeftHigh.length = _
          rw [highAsArm]
        have reductRuns : stepCapArc (runArcCell state betaLeftMid betaRight
              (RawTwoCellExpr.gen genBeta)) capPosition
            = stepCapArc (stepCapArc state (gapVal + 2 + capPosition)) capPosition := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCapArc state
            (SpineAtom.mk _ _ betaLeftMid betaDom betaCod genBeta betaRight) domTwo codZero]
          show stepCapArc (stepCapArc state betaLeftMid.length) capPosition = _
          rw [midAsArm]
        refine ⟨blockRotate state.nextFresh 1 1, ?_, ?_⟩
        · rw [redexRuns]
          exact arcBoundedSwapCarrier_blockRotate state.nextFresh 1 1 (Nat.le_refl _)
            (Nat.le_refl _)
        · rw [redexRuns, reductRuns]
          exact armInstance
    | inl isCup =>
        obtain ⟨domZeroBeq, codTwoBeq⟩ := boolBothTrueOfAndTrue isCup
        have domZero : betaDom.length = 0 := of_decide_eq_true domZeroBeq
        have codTwo : betaCod.length = 2 := of_decide_eq_true codTwoBeq
        have armInstance := arcDisjointCapCupSwapSimCount_ofWellFormed state capPosition gapVal
          wellFormed
          (by rw [← prefixAsArmA, openLen]; exact Nat.le_add_right _ _)
        have redexRuns : runArcCell (stepCapArc state capPosition) betaLeftHigh betaRight
            (RawTwoCellExpr.gen genBeta)
            = stepCupArc (stepCapArc state capPosition) (gapVal + capPosition) := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCupArc (stepCapArc state capPosition)
            (SpineAtom.mk _ _ betaLeftHigh betaDom betaCod genBeta betaRight) domZero codTwo]
          show stepCupArc (stepCapArc state capPosition) betaLeftHigh.length = _
          rw [highAsArm]
        have reductRuns : stepCapArc (runArcCell state betaLeftMid betaRight
              (RawTwoCellExpr.gen genBeta)) capPosition
            = stepCapArc (stepCupArc state (gapVal + 2 + capPosition)) capPosition := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCupArc state
            (SpineAtom.mk _ _ betaLeftMid betaDom betaCod genBeta betaRight) domZero codTwo]
          show stepCapArc (stepCupArc state betaLeftMid.length) capPosition = _
          rw [midAsArm]
        refine ⟨blockRotate state.nextFresh 1 3, ?_, ?_⟩
        · rw [redexRuns]
          exact arcBoundedSwapCarrier_blockRotate state.nextFresh 1 3 (Nat.le_refl _)
            (Nat.le_refl _)
        · rw [redexRuns, reductRuns]
          exact armInstance
  | _, _, betaDom, betaCod, .vcomp betaOne betaTwo, betaLeftHigh, betaLeftMid, betaRight, state,
      prefixWires, domSegment, suffixWires, capPosition, wellFormed, isTurnback, decomp,
      prefixLen, highLen, segLen, capWindow, guardLeftHyp, guardRightHyp => by
    obtain ⟨oneTurnback, twoTurnback⟩ := boolBothTrueOfAndTrue isTurnback
    obtain ⟨pipeSegment, decompPipe, pipeLen, probeFactsOne⟩ :=
      arcCellSegmentRun_ofWellFormed betaOne betaLeftMid betaRight state prefixWires domSegment
        suffixWires wellFormed oneTurnback decomp prefixLen segLen
    obtain ⟨sigmaOne, carrierOne, simOne⟩ :=
      arcCapAtomPastCellSwapSimCount betaOne betaLeftHigh betaLeftMid betaRight state prefixWires
        domSegment suffixWires capPosition wellFormed oneTurnback decomp prefixLen highLen segLen
        capWindow guardLeftHyp guardRightHyp
    have wellFormedRedexOne : WellFormedArcState
        (runArcCell (stepCapArc state capPosition) betaLeftHigh betaRight betaOne) :=
      wellFormedArcState_runArcCell _ betaLeftHigh betaRight betaOne
        (wellFormedArcState_stepCapArc state capPosition wellFormed)
    have wellFormedMid : WellFormedArcState (runArcCell state betaLeftMid betaRight betaOne) :=
      wellFormedArcState_runArcCell state betaLeftMid betaRight betaOne wellFormed
    have wellFormedReductOne : WellFormedArcState
        (stepCapArc (runArcCell state betaLeftMid betaRight betaOne) capPosition) :=
      wellFormedArcState_stepCapArc _ capPosition wellFormedMid
    obtain ⟨simExt, carrierExt⟩ := arcStepSimCount_extendByCommonCell sigmaOne state.nextFresh
      wellFormed.isNonDegenerate _ _ wellFormedRedexOne wellFormedReductOne betaLeftHigh betaRight
      betaTwo carrierOne simOne
    -- the cap reads and their transported guards at the intermediate state
    have capPosSuccBelowPrefix : capPosition + 1 < prefixWires.length := capWindow
    have capPosBelowPrefix : capPosition < prefixWires.length :=
      Nat.lt_of_le_of_lt (Nat.le_succ capPosition) capPosSuccBelowPrefix
    have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
      fun edge edgeMem => (wellFormed.isFresh.2.1 edge edgeMem).2
    have capPosBelowWires : capPosition < state.openWires.length := by
      rw [decomp, lengthAppend prefixWires (domSegment ++ suffixWires)]
      exact Nat.lt_of_lt_of_le capPosBelowPrefix (Nat.le_add_right _ _)
    have capPosSuccBelowWires : capPosition + 1 < state.openWires.length := by
      rw [decomp, lengthAppend prefixWires (domSegment ++ suffixWires)]
      exact Nat.lt_of_lt_of_le capPosSuccBelowPrefix (Nat.le_add_right _ _)
    have readLeftRootBelow : unionFindRootOf state.links
        (natListGetAt state.openWires capPosition) < state.nextFresh :=
      unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow _
        (wellFormed.isFresh.1 _ (natListGetAt_memOfBelow state.openWires capPosition
          capPosBelowWires))
    have readRightRootBelow : unionFindRootOf state.links
        (natListGetAt state.openWires (capPosition + 1)) < state.nextFresh :=
      unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow _
        (wellFormed.isFresh.1 _ (natListGetAt_memOfBelow state.openWires (capPosition + 1)
          capPosSuccBelowWires))
    obtain ⟨_, disjointPipeLeft, _⟩ :=
      probeFactsOne (natListGetAt state.openWires capPosition) readLeftRootBelow guardLeftHyp
    obtain ⟨_, disjointPipeRight, _⟩ :=
      probeFactsOne (natListGetAt state.openWires (capPosition + 1)) readRightRootBelow
        guardRightHyp
    have readLeftStable : natListGetAt
          (runArcCell state betaLeftMid betaRight betaOne).openWires capPosition
        = natListGetAt state.openWires capPosition := by
      rw [decompPipe, decomp,
        natListGetAt_appendBelow prefixWires (pipeSegment ++ suffixWires) capPosition
          capPosBelowPrefix,
        natListGetAt_appendBelow prefixWires (domSegment ++ suffixWires) capPosition
          capPosBelowPrefix]
    have readRightStable : natListGetAt
          (runArcCell state betaLeftMid betaRight betaOne).openWires (capPosition + 1)
        = natListGetAt state.openWires (capPosition + 1) := by
      rw [decompPipe, decomp,
        natListGetAt_appendBelow prefixWires (pipeSegment ++ suffixWires) (capPosition + 1)
          capPosSuccBelowPrefix,
        natListGetAt_appendBelow prefixWires (domSegment ++ suffixWires) (capPosition + 1)
          capPosSuccBelowPrefix]
    obtain ⟨sigmaTwo, carrierTwo, simTwo⟩ :=
      arcCapAtomPastCellSwapSimCount betaTwo betaLeftHigh betaLeftMid betaRight
        (runArcCell state betaLeftMid betaRight betaOne) prefixWires pipeSegment suffixWires
        capPosition wellFormedMid twoTurnback decompPipe prefixLen highLen pipeLen capWindow
        (by rw [readLeftStable]; exact disjointPipeLeft)
        (by rw [readRightStable]; exact disjointPipeRight)
    refine ⟨fun node => sigmaTwo (sigmaOne node), ?_, ?_⟩
    · rw [runArcCell_vcomp]
      exact arcBoundedSwapCarrier_comp carrierExt
        (arcBoundedSwapCarrier_weaken carrierTwo
          (runArcCell_nextFresh_le state betaLeftMid betaRight betaOne)
          (Nat.le_of_eq simExt.nfEq.symm))
    · rw [runArcCell_vcomp, runArcCell_vcomp]
      exact arcStepSimCount_comp sigmaOne sigmaTwo _ _ _ simExt simTwo
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodyDom bodyCod body, betaLeftHigh,
      betaLeftMid, betaRight, state, prefixWires, domSegment, suffixWires, capPosition,
      wellFormed, isTurnback, decomp, prefixLen, highLen, segLen, capWindow, guardLeftHyp,
      guardRightHyp => by
    have domLenSplit : domSegment.length = oneCell.length + bodyDom.length := by
      rw [segLen]
      exact ModalityPath.length_composePath oneCell bodyDom
    obtain ⟨oneSegment, bodyDomSegment, segSplit, oneSegLen⟩ :=
      natListSplitAtLength domSegment oneCell.length
        (by rw [domLenSplit]; exact Nat.le_add_right _ _)
    have bodyDomSegLen : bodyDomSegment.length = bodyDom.length := by
      have totalLen : oneSegment.length + bodyDomSegment.length
          = oneCell.length + bodyDom.length := by
        rw [← lengthAppend oneSegment bodyDomSegment, ← segSplit]
        exact domLenSplit
      rw [oneSegLen] at totalLen
      exact natAddLeftCancelSeg oneCell.length _ _ totalLen
    have decompShifted : state.openWires
        = (prefixWires ++ oneSegment) ++ (bodyDomSegment ++ suffixWires) := by
      rw [decomp, segSplit, natListAppendAssoc oneSegment bodyDomSegment suffixWires,
        ← natListAppendAssoc prefixWires oneSegment (bodyDomSegment ++ suffixWires)]
    have prefixLenShifted : (prefixWires ++ oneSegment).length
        = (composePath betaLeftMid oneCell).length := by
      rw [lengthAppend prefixWires oneSegment,
        ModalityPath.length_composePath betaLeftMid oneCell, prefixLen, oneSegLen]
    have highLenShifted : (composePath betaLeftHigh oneCell).length + 2
        = (composePath betaLeftMid oneCell).length := by
      rw [ModalityPath.length_composePath betaLeftHigh oneCell,
        ModalityPath.length_composePath betaLeftMid oneCell,
        Nat.add_right_comm betaLeftHigh.length oneCell.length 2, highLen]
    have capWindowShifted : capPosition + 2 ≤ (prefixWires ++ oneSegment).length :=
      Nat.le_trans capWindow (by rw [lengthAppend]; exact Nat.le_add_right _ _)
    obtain ⟨sigma, carrier, simulation⟩ :=
      arcCapAtomPastCellSwapSimCount body (composePath betaLeftHigh oneCell)
        (composePath betaLeftMid oneCell) betaRight state (prefixWires ++ oneSegment)
        bodyDomSegment suffixWires capPosition wellFormed isTurnback decompShifted
        prefixLenShifted highLenShifted bodyDomSegLen capWindowShifted
        (fun wire wireMem => guardLeftHyp wire
          (by rw [segSplit]; exact natListMem_appendOfRight oneSegment bodyDomSegment wireMem))
        (fun wire wireMem => guardRightHyp wire
          (by rw [segSplit]; exact natListMem_appendOfRight oneSegment bodyDomSegment wireMem))
    exact ⟨sigma, carrier, simulation⟩
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ bodyDom bodyCod oneCell body, betaLeftHigh,
      betaLeftMid, betaRight, state, prefixWires, domSegment, suffixWires, capPosition,
      wellFormed, isTurnback, decomp, prefixLen, highLen, segLen, capWindow, guardLeftHyp,
      guardRightHyp => by
    have domLenSplit : domSegment.length = bodyDom.length + oneCell.length := by
      rw [segLen]
      exact ModalityPath.length_composePath bodyDom oneCell
    obtain ⟨bodyDomSegment, oneSegment, segSplit, bodySegLen⟩ :=
      natListSplitAtLength domSegment bodyDom.length
        (by rw [domLenSplit]; exact Nat.le_add_right _ _)
    have decompShifted : state.openWires
        = prefixWires ++ (bodyDomSegment ++ (oneSegment ++ suffixWires)) := by
      rw [decomp, segSplit, natListAppendAssoc bodyDomSegment oneSegment suffixWires]
    obtain ⟨sigma, carrier, simulation⟩ :=
      arcCapAtomPastCellSwapSimCount body betaLeftHigh betaLeftMid
        (composePath oneCell betaRight) state prefixWires bodyDomSegment
        (oneSegment ++ suffixWires) capPosition wellFormed isTurnback decompShifted prefixLen
        highLen bodySegLen capWindow
        (fun wire wireMem => guardLeftHyp wire
          (by rw [segSplit]; exact natListMem_appendOfLeft bodyDomSegment oneSegment wireMem))
        (fun wire wireMem => guardRightHyp wire
          (by rw [segSplit]; exact natListMem_appendOfLeft bodyDomSegment oneSegment wireMem))
    exact ⟨sigma, carrier, simulation⟩

/-! ## `atomPastCell`, cup side (unguarded) -/

/-- ★★ **A CUP commutes past a WHOLE turnback-only cell** (the r27-named `atomPastCell`, cup
side).  The cup splices at `cupPosition` inside the prefix (`cupPosition <= |prefix|`); the cell
runs inside the window (`|betaLeftMid| = |prefix|` before the cup, `|betaLeftHigh| = |prefix| + 2`
after it).  NO component guard: the cup's legs are fresh, so every pairwise arm is unguarded —
exactly the r27 doctrine's fresh-block exemption, now at whole-cell reach. -/
theorem arcCupAtomPastCellSwapSimCount {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {betaLocalSource betaLocalTarget : signature.graph.Mode} →
    {betaDom betaCod : ModalityPath signature.graph betaLocalSource betaLocalTarget} →
    (cellBeta : RawTwoCellExpr signature betaDom betaCod) →
    (betaLeftHigh betaLeftMid : ModalityPath signature.graph overallSource betaLocalSource) →
    (betaRight : ModalityPath signature.graph betaLocalTarget overallTarget) →
    (state : ArcWireState) → (prefixWires domSegment suffixWires : List Nat) →
    (cupPosition : Nat) →
    WellFormedArcState state →
    cellBeta.isTurnbackOnly = true →
    state.openWires = prefixWires ++ (domSegment ++ suffixWires) →
    prefixWires.length = betaLeftMid.length →
    betaLeftHigh.length = betaLeftMid.length + 2 →
    domSegment.length = betaDom.length →
    cupPosition ≤ prefixWires.length →
    ∃ sigma,
      ArcBoundedSwapCarrier state.nextFresh
          (runArcCell (stepCupArc state cupPosition) betaLeftHigh betaRight cellBeta).nextFresh
          sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (stepCupArc state cupPosition) betaLeftHigh betaRight cellBeta)
            (stepCupArc (runArcCell state betaLeftMid betaRight cellBeta) cupPosition)
  | _, _, _, _, .id _, betaLeftHigh, betaLeftMid, betaRight, state, prefixWires, domSegment,
      suffixWires, cupPosition, wellFormed, _, _, _, _, _, _ =>
    ⟨fun node => node,
     arcBoundedSwapCarrier_identity state.nextFresh (stepCupArc state cupPosition).nextFresh,
     arcStepSimCount_refl (stepCupArc state cupPosition)
       (isUnionFindForest_stepCupArc state cupPosition wellFormed.isForest)⟩
  | _, _, betaDom, betaCod, .gen genBeta, betaLeftHigh, betaLeftMid, betaRight, state,
      prefixWires, domSegment, suffixWires, cupPosition, wellFormed, isTurnback, decomp,
      prefixLen, highLen, segLen, cupWindow => by
    obtain ⟨gapVal, gapEq⟩ : ∃ gapValue, gapValue + cupPosition = prefixWires.length :=
      ⟨prefixWires.length - cupPosition, subAddCancel cupPosition prefixWires.length cupWindow⟩
    have prefixAsArm : prefixWires.length = gapVal + cupPosition := gapEq.symm
    have midAsArm : betaLeftMid.length = gapVal + cupPosition := prefixLen.symm.trans prefixAsArm
    have highAsArm : betaLeftHigh.length = gapVal + 2 + cupPosition := by
      rw [highLen, midAsArm, Nat.add_right_comm gapVal cupPosition 2,
        Nat.add_right_comm gapVal 2 cupPosition]
    have openLen : state.openWires.length
        = prefixWires.length + (domSegment ++ suffixWires).length := by
      rw [decomp]
      exact lengthAppend prefixWires (domSegment ++ suffixWires)
    cases boolEitherTrueOfOrTrue isTurnback with
    | inr isCap =>
        obtain ⟨domTwoBeq, codZeroBeq⟩ := boolBothTrueOfAndTrue isCap
        have domTwo : betaDom.length = 2 := of_decide_eq_true domTwoBeq
        have codZero : betaCod.length = 0 := of_decide_eq_true codZeroBeq
        obtain ⟨readLeftWire, readRightWire, segPair⟩ :=
          natListEqPairOfLengthTwo domSegment (segLen.trans domTwo)
        subst segPair
        have windowArm : gapVal + cupPosition + 2 ≤ state.openWires.length := by
          rw [← prefixAsArm, openLen, lengthAppend [readLeftWire, readRightWire] suffixWires]
          exact Nat.add_le_add_left (Nat.le_add_right 2 suffixWires.length) prefixWires.length
        have armInstance := arcDisjointCupCapSwapSimCount_ofWellFormed state cupPosition gapVal
          wellFormed windowArm
        have redexRuns : runArcCell (stepCupArc state cupPosition) betaLeftHigh betaRight
            (RawTwoCellExpr.gen genBeta)
            = stepCapArc (stepCupArc state cupPosition) (gapVal + 2 + cupPosition) := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCapArc (stepCupArc state cupPosition)
            (SpineAtom.mk _ _ betaLeftHigh betaDom betaCod genBeta betaRight) domTwo codZero]
          show stepCapArc (stepCupArc state cupPosition) betaLeftHigh.length = _
          rw [highAsArm]
        have reductRuns : stepCupArc (runArcCell state betaLeftMid betaRight
              (RawTwoCellExpr.gen genBeta)) cupPosition
            = stepCupArc (stepCapArc state (gapVal + cupPosition)) cupPosition := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCapArc state
            (SpineAtom.mk _ _ betaLeftMid betaDom betaCod genBeta betaRight) domTwo codZero]
          show stepCupArc (stepCapArc state betaLeftMid.length) cupPosition = _
          rw [midAsArm]
        refine ⟨blockRotate state.nextFresh 3 1, ?_, ?_⟩
        · rw [redexRuns]
          exact arcBoundedSwapCarrier_blockRotate state.nextFresh 3 1 (Nat.le_refl _)
            (Nat.le_refl _)
        · rw [redexRuns, reductRuns]
          exact armInstance
    | inl isCup =>
        obtain ⟨domZeroBeq, codTwoBeq⟩ := boolBothTrueOfAndTrue isCup
        have domZero : betaDom.length = 0 := of_decide_eq_true domZeroBeq
        have codTwo : betaCod.length = 2 := of_decide_eq_true codTwoBeq
        have windowArm : gapVal + cupPosition ≤ state.openWires.length := by
          rw [← prefixAsArm, openLen]
          exact Nat.le_add_right _ _
        have armInstance := twoCupGodement_arcStepSimCount state cupPosition gapVal
          wellFormed.isFresh windowArm wellFormed.isForest
        have redexRuns : runArcCell (stepCupArc state cupPosition) betaLeftHigh betaRight
            (RawTwoCellExpr.gen genBeta)
            = stepCupArc (stepCupArc state cupPosition) (gapVal + 2 + cupPosition) := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCupArc (stepCupArc state cupPosition)
            (SpineAtom.mk _ _ betaLeftHigh betaDom betaCod genBeta betaRight) domZero codTwo]
          show stepCupArc (stepCupArc state cupPosition) betaLeftHigh.length = _
          rw [highAsArm]
        have reductRuns : stepCupArc (runArcCell state betaLeftMid betaRight
              (RawTwoCellExpr.gen genBeta)) cupPosition
            = stepCupArc (stepCupArc state (gapVal + cupPosition)) cupPosition := by
          rw [runArcCell_gen, stepArcAtom_eq_stepCupArc state
            (SpineAtom.mk _ _ betaLeftMid betaDom betaCod genBeta betaRight) domZero codTwo]
          show stepCupArc (stepCupArc state betaLeftMid.length) cupPosition = _
          rw [midAsArm]
        refine ⟨blockRotate state.nextFresh 3 3, ?_, ?_⟩
        · rw [redexRuns]
          exact arcBoundedSwapCarrier_blockRotate state.nextFresh 3 3 (Nat.le_refl _)
            (Nat.le_refl _)
        · rw [redexRuns, reductRuns]
          exact armInstance
  | _, _, betaDom, betaCod, .vcomp betaOne betaTwo, betaLeftHigh, betaLeftMid, betaRight, state,
      prefixWires, domSegment, suffixWires, cupPosition, wellFormed, isTurnback, decomp,
      prefixLen, highLen, segLen, cupWindow => by
    obtain ⟨oneTurnback, twoTurnback⟩ := boolBothTrueOfAndTrue isTurnback
    obtain ⟨pipeSegment, decompPipe, pipeLen, _⟩ :=
      arcCellSegmentRun_ofWellFormed betaOne betaLeftMid betaRight state prefixWires domSegment
        suffixWires wellFormed oneTurnback decomp prefixLen segLen
    obtain ⟨sigmaOne, carrierOne, simOne⟩ :=
      arcCupAtomPastCellSwapSimCount betaOne betaLeftHigh betaLeftMid betaRight state prefixWires
        domSegment suffixWires cupPosition wellFormed oneTurnback decomp prefixLen highLen segLen
        cupWindow
    have wellFormedRedexOne : WellFormedArcState
        (runArcCell (stepCupArc state cupPosition) betaLeftHigh betaRight betaOne) :=
      wellFormedArcState_runArcCell _ betaLeftHigh betaRight betaOne
        (wellFormedArcState_stepCupArc state cupPosition wellFormed)
    have wellFormedMid : WellFormedArcState (runArcCell state betaLeftMid betaRight betaOne) :=
      wellFormedArcState_runArcCell state betaLeftMid betaRight betaOne wellFormed
    have wellFormedReductOne : WellFormedArcState
        (stepCupArc (runArcCell state betaLeftMid betaRight betaOne) cupPosition) :=
      wellFormedArcState_stepCupArc _ cupPosition wellFormedMid
    obtain ⟨simExt, carrierExt⟩ := arcStepSimCount_extendByCommonCell sigmaOne state.nextFresh
      wellFormed.isNonDegenerate _ _ wellFormedRedexOne wellFormedReductOne betaLeftHigh betaRight
      betaTwo carrierOne simOne
    obtain ⟨sigmaTwo, carrierTwo, simTwo⟩ :=
      arcCupAtomPastCellSwapSimCount betaTwo betaLeftHigh betaLeftMid betaRight
        (runArcCell state betaLeftMid betaRight betaOne) prefixWires pipeSegment suffixWires
        cupPosition wellFormedMid twoTurnback decompPipe prefixLen highLen pipeLen cupWindow
    refine ⟨fun node => sigmaTwo (sigmaOne node), ?_, ?_⟩
    · rw [runArcCell_vcomp]
      exact arcBoundedSwapCarrier_comp carrierExt
        (arcBoundedSwapCarrier_weaken carrierTwo
          (runArcCell_nextFresh_le state betaLeftMid betaRight betaOne)
          (Nat.le_of_eq simExt.nfEq.symm))
    · rw [runArcCell_vcomp, runArcCell_vcomp]
      exact arcStepSimCount_comp sigmaOne sigmaTwo _ _ _ simExt simTwo
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodyDom bodyCod body, betaLeftHigh,
      betaLeftMid, betaRight, state, prefixWires, domSegment, suffixWires, cupPosition,
      wellFormed, isTurnback, decomp, prefixLen, highLen, segLen, cupWindow => by
    have domLenSplit : domSegment.length = oneCell.length + bodyDom.length := by
      rw [segLen]
      exact ModalityPath.length_composePath oneCell bodyDom
    obtain ⟨oneSegment, bodyDomSegment, segSplit, oneSegLen⟩ :=
      natListSplitAtLength domSegment oneCell.length
        (by rw [domLenSplit]; exact Nat.le_add_right _ _)
    have bodyDomSegLen : bodyDomSegment.length = bodyDom.length := by
      have totalLen : oneSegment.length + bodyDomSegment.length
          = oneCell.length + bodyDom.length := by
        rw [← lengthAppend oneSegment bodyDomSegment, ← segSplit]
        exact domLenSplit
      rw [oneSegLen] at totalLen
      exact natAddLeftCancelSeg oneCell.length _ _ totalLen
    have decompShifted : state.openWires
        = (prefixWires ++ oneSegment) ++ (bodyDomSegment ++ suffixWires) := by
      rw [decomp, segSplit, natListAppendAssoc oneSegment bodyDomSegment suffixWires,
        ← natListAppendAssoc prefixWires oneSegment (bodyDomSegment ++ suffixWires)]
    have prefixLenShifted : (prefixWires ++ oneSegment).length
        = (composePath betaLeftMid oneCell).length := by
      rw [lengthAppend prefixWires oneSegment,
        ModalityPath.length_composePath betaLeftMid oneCell, prefixLen, oneSegLen]
    have highLenShifted : (composePath betaLeftHigh oneCell).length
        = (composePath betaLeftMid oneCell).length + 2 := by
      rw [ModalityPath.length_composePath betaLeftHigh oneCell,
        ModalityPath.length_composePath betaLeftMid oneCell, highLen,
        Nat.add_right_comm betaLeftMid.length 2 oneCell.length]
    have cupWindowShifted : cupPosition ≤ (prefixWires ++ oneSegment).length :=
      Nat.le_trans cupWindow (by rw [lengthAppend]; exact Nat.le_add_right _ _)
    obtain ⟨sigma, carrier, simulation⟩ :=
      arcCupAtomPastCellSwapSimCount body (composePath betaLeftHigh oneCell)
        (composePath betaLeftMid oneCell) betaRight state (prefixWires ++ oneSegment)
        bodyDomSegment suffixWires cupPosition wellFormed isTurnback decompShifted
        prefixLenShifted highLenShifted bodyDomSegLen cupWindowShifted
    exact ⟨sigma, carrier, simulation⟩
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ bodyDom bodyCod oneCell body, betaLeftHigh,
      betaLeftMid, betaRight, state, prefixWires, domSegment, suffixWires, cupPosition,
      wellFormed, isTurnback, decomp, prefixLen, highLen, segLen, cupWindow => by
    have domLenSplit : domSegment.length = bodyDom.length + oneCell.length := by
      rw [segLen]
      exact ModalityPath.length_composePath bodyDom oneCell
    obtain ⟨bodyDomSegment, oneSegment, segSplit, bodySegLen⟩ :=
      natListSplitAtLength domSegment bodyDom.length
        (by rw [domLenSplit]; exact Nat.le_add_right _ _)
    have decompShifted : state.openWires
        = prefixWires ++ (bodyDomSegment ++ (oneSegment ++ suffixWires)) := by
      rw [decomp, segSplit, natListAppendAssoc bodyDomSegment oneSegment suffixWires]
    obtain ⟨sigma, carrier, simulation⟩ :=
      arcCupAtomPastCellSwapSimCount body betaLeftHigh betaLeftMid
        (composePath oneCell betaRight) state prefixWires bodyDomSegment
        (oneSegment ++ suffixWires) cupPosition wellFormed isTurnback decompShifted prefixLen
        highLen bodySegLen cupWindow
    exact ⟨sigma, carrier, simulation⟩

/-! ## Fires — the atom past the THREE-atom cell (both alpha colours), machine-instantiated -/

/-- The four-wire fire seed: boundary wires `[0,1,2,3]`, empty forest, frontier `4`. -/
def arcAtomPastCellFireSeed : ArcWireState := ArcWireState.mk [0, 1, 2, 3] [] 4 0 [] []

/-- The four-wire fire seed is well-formed. -/
theorem arcAtomPastCellFireSeed_isWellFormed : WellFormedArcState arcAtomPastCellFireSeed :=
  ⟨by unfold ArcStateFresh arcAtomPastCellFireSeed; decide, trivial, by decide⟩

/-- ★ **`atomPastCell` FIRED, cap side, against the THREE-atom cell**: a cap at position `1`
commutes past the whole cup/cup/cap fixture running in the window at `[4, +0)` — the guard
hypotheses are vacuous (the fixture's dom segment is empty), the window bookkeeping is
`|betaLeftMid| = 4 = |prefix|`, `|betaLeftHigh| = 2`. -/
theorem arcCapAtomPastThreeAtomCell_fired :
    ∃ sigma,
      ArcBoundedSwapCarrier arcAtomPastCellFireSeed.nextFresh
          (runArcCell (stepCapArc arcAtomPastCellFireSeed 1) adjunctionLeftThenRight
            (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
            threeAtomTurnbackCell).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (stepCapArc arcAtomPastCellFireSeed 1) adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell)
            (stepCapArc (runArcCell arcAtomPastCellFireSeed
              (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell) 1) :=
  arcCapAtomPastCellSwapSimCount threeAtomTurnbackCell adjunctionLeftThenRight
    (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) arcAtomPastCellFireSeed
    [0, 1, 2, 3] [] [] 1 arcAtomPastCellFireSeed_isWellFormed
    threeAtomTurnbackCell_isTurnbackOnly rfl rfl rfl rfl (by decide)
    (fun wire wireMem => nomatch wireMem) (fun wire wireMem => nomatch wireMem)

/-- The two-wire fire seed for the cup side. -/
def arcCupPastCellFireSeed : ArcWireState := ArcWireState.mk [0, 1] [] 2 0 [] []

/-- The two-wire fire seed is well-formed. -/
theorem arcCupPastCellFireSeed_isWellFormed : WellFormedArcState arcCupPastCellFireSeed :=
  ⟨by unfold ArcStateFresh arcCupPastCellFireSeed; decide, trivial, by decide⟩

/-- ★ **`atomPastCell` FIRED, cup side, against the THREE-atom cell**: a cup splicing at
position `1` commutes past the whole fixture (`|betaLeftMid| = 2`, `|betaLeftHigh| = 4`). -/
theorem arcCupAtomPastThreeAtomCell_fired :
    ∃ sigma,
      ArcBoundedSwapCarrier arcCupPastCellFireSeed.nextFresh
          (runArcCell (stepCupArc arcCupPastCellFireSeed 1)
            (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
            (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
            threeAtomTurnbackCell).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (stepCupArc arcCupPastCellFireSeed 1)
              (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell)
            (stepCupArc (runArcCell arcCupPastCellFireSeed adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell) 1) :=
  arcCupAtomPastCellSwapSimCount threeAtomTurnbackCell
    (composePath adjunctionLeftThenRight adjunctionLeftThenRight) adjunctionLeftThenRight
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) arcCupPastCellFireSeed
    [0, 1] [] [] 1 arcCupPastCellFireSeed_isWellFormed threeAtomTurnbackCell_isTurnbackOnly
    rfl rfl rfl rfl (by decide)

/-! ## Honesty marker + pins -/

/-- **Honesty marker — `atomPastCell` is SHIPPED, both atom colours.**  One cap (guarded by the
segment-transported component invariant) or one cup (unguarded) commutes past a whole
turnback-only cell, with a bounded composite carrier; the vcomp crux (guard re-establishment at
intermediate states) is discharged by the r28 segment-run engine; fired against the three-atom
cup/cup/cap fixture from two seeds.  `= true`. -/
def fxMode_hasArcAtomPastCellSwapSimCount : Bool := true

/-- **Honesty pin — the whole-cell disjoint whisker-support target stays OPEN** (the atom side is
still a single atom; `cellPastCell` is Brick 3).  `rfl`. -/
theorem arcAtomPastCell_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — residual (2)'s renameable-level marker stays OPEN.**  `rfl`. -/
theorem arcAtomPastCell_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN.**  `rfl`. -/
theorem arcAtomPastCell_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  `rfl`. -/
theorem arcAtomPastCell_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
