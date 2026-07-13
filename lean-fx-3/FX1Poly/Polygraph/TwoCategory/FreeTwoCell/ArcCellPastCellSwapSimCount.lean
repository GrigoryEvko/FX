import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcAtomPastCellSwapSimCount

/-! # MODE-COMMUTE r28 — `cellPastCell`: a WHOLE cell commutes past a WHOLE cell (the double induction CLOSED)

## What this ships (Brick 3 of the whole-cell fold — THE WHOLE-CELL THEOREM)

The r27-named double induction `atomPastCell -> cellPastCell`, closed.  Two turnback-only cells
in the Godement configuration — `cellAlpha` in the f-window (starting at `|alphaLeft|`),
`cellBeta` in the g-window (starting at `|alphaLeft| + |fX| + |gapPath|`) — run in either order
from a `WellFormedArcState` whose openWires decompose as
`leftPad ++ fSegment ++ gapSegment ++ gSegment ++ suffix`, are related by a full eight-field
`ArcStepSimCount` with a bounded composite carrier, PROVIDED the two windows are
component-disjoint (`∀ fWire ∈ fSegment, ∀ gWire ∈ gSegment, isSameComponent = false` — the r26
machine-forced guard, which the r26 counterexample shows cannot be dropped).

The alpha-side induction mirrors Brick 2's beta-side one:

  * `.gen` — Brick 2's `atomPastCell` (cap side consuming the windows-disjointness pointwise,
    cup side unguarded), positions produced by the path-length bookkeeping;
  * `.vcomp` — swap `alphaTwo` past the whole `cellBeta` from the post-`alphaOne` state (IH, with
    the f-window decomposition AND the windows-disjointness transported through `alphaOne` by the
    r28 segment-run engine, probe = each g-wire), then swap `alphaOne` past `cellBeta` (IH) and
    extend by the common suffix `alphaTwo`; chain by `arcStepSimCount_comp`;
  * whiskers — `composePath_assoc` re-association of the beta whiskers, segment re-splits; the
    `whiskerRight` case migrates the whisker into the GAP (`gapPath := composePath one gapPath`)
    — the reason the statement carries an explicit gap between the windows.

The two alpha right whiskers are free parameters (the state action never reads them), so the
statement instantiates directly at the `ArcGodementCoreSwapSimCount` inner shape (gap zero,
`betaLeft = composePath alphaLeft fX`) — that packaging is Brick 4's.

## Honesty

The pins stay `false` in THIS file too: the `:234` verbatim demand is a links-LIST equality (a
different, order-sensitive shape — Brick 4 adjudicates it), `:3046` residual (2) demands the
existential over ARBITRARY well-formed states with NO window decomposition and NO disjointness
guard and over cells with BOX atoms — this brick is the guarded turnback-only core, not that
literal statement.  Brick 4 records the deltas precisely.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` + independent
`#print axioms` in the twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Component-disjointness is symmetric (root `==` flipped through `Ne.symm`). -/
theorem isSameComponentFalse_symm {links : List (Nat × Nat)} {firstNode secondNode : Nat}
    (disjoint : isSameComponent links firstNode secondNode = false) :
    isSameComponent links secondNode firstNode = false :=
  natBeqFalseOfNe (Ne.symm (neOfBeqFalse disjoint))

/-- The two-window component-disjointness invariant: every f-window wire is component-disjoint
from every g-window wire.  The seed-level guard `cellPastCell` threads (pointwise an
`arcProbeDisjointFromSegment` per f-wire). -/
def arcWindowsComponentDisjoint (links : List (Nat × Nat))
    (fWindow gWindow : List Nat) : Prop :=
  ∀ fWire ∈ fWindow, arcProbeDisjointFromSegment links fWire gWindow

/-! ## `cellPastCell` — the whole-cell double induction -/

/-- ★★★ **`cellPastCell` — a WHOLE turnback-only cell commutes past a WHOLE turnback-only cell.**
The r27 grind target: `cellAlpha : fMid => fHigh` (f-window at `|alphaLeft|`) and
`cellBeta : betaDom => betaCod` (g-window at `|alphaLeft| + |fX| + |gapPath|`), run in either
order from a decomposed well-formed state with component-disjoint windows, are
`ArcStepSimCount`-related by a bounded composite carrier.  The beta whiskers are the STRUCTURAL
composites `alphaLeft . fX . gapPath`, so the statement specializes on the nose to the Godement
inner shape at `gapPath := identityPath`.  Both alpha right whiskers are free (the arc action
never reads them). -/
theorem arcCellPastCellSwapSimCount {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {alphaLocalSource alphaLocalTarget : signature.graph.Mode} →
    {fMid fHigh : ModalityPath signature.graph alphaLocalSource alphaLocalTarget} →
    (cellAlpha : RawTwoCellExpr signature fMid fHigh) →
    {betaLocalSource betaLocalTarget : signature.graph.Mode} →
    {betaDom betaCod : ModalityPath signature.graph betaLocalSource betaLocalTarget} →
    (cellBeta : RawTwoCellExpr signature betaDom betaCod) →
    (alphaLeft : ModalityPath signature.graph overallSource alphaLocalSource) →
    (gapPath : ModalityPath signature.graph alphaLocalTarget betaLocalSource) →
    (alphaRightRedex alphaRightReduct :
      ModalityPath signature.graph alphaLocalTarget overallTarget) →
    (betaRight : ModalityPath signature.graph betaLocalTarget overallTarget) →
    (state : ArcWireState) →
    (leftPad fSegment gapSegment gSegment suffixWires : List Nat) →
    WellFormedArcState state →
    cellAlpha.isTurnbackOnly = true →
    cellBeta.isTurnbackOnly = true →
    state.openWires = leftPad ++ (fSegment ++ (gapSegment ++ (gSegment ++ suffixWires))) →
    leftPad.length = alphaLeft.length →
    fSegment.length = fMid.length →
    gapSegment.length = gapPath.length →
    gSegment.length = betaDom.length →
    arcWindowsComponentDisjoint state.links fSegment gSegment →
    ∃ sigma,
      ArcBoundedSwapCarrier state.nextFresh
          (runArcCell (runArcCell state alphaLeft alphaRightRedex cellAlpha)
            (composePath alphaLeft (composePath fHigh gapPath)) betaRight cellBeta).nextFresh
          sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (runArcCell state alphaLeft alphaRightRedex cellAlpha)
              (composePath alphaLeft (composePath fHigh gapPath)) betaRight cellBeta)
            (runArcCell (runArcCell state
                (composePath alphaLeft (composePath fMid gapPath)) betaRight cellBeta)
              alphaLeft alphaRightReduct cellAlpha)
  | _, _, _, _, .id _, _, _, _, _, cellBeta, alphaLeft, gapPath, alphaRightRedex, alphaRightReduct,
      betaRight, state, leftPad, fSegment, gapSegment, gSegment, suffixWires, wellFormed, _,
      _, _, _, _, _, _, _ =>
    ⟨fun node => node,
     arcBoundedSwapCarrier_identity state.nextFresh _,
     arcStepSimCount_refl _
       (wellFormedArcState_runArcCell state _ betaRight cellBeta wellFormed).isForest⟩
  | _, _, fMid, fHigh, .gen genAlpha, _, _, _, _, cellBeta, alphaLeft, gapPath, alphaRightRedex,
      alphaRightReduct, betaRight, state, leftPad, fSegment, gapSegment, gSegment, suffixWires,
      wellFormed, alphaTurnback, betaTurnback, decomp, padLen, fSegLen, gapLen, gSegLen,
      windowsDisjoint => by
    have decompShifted : state.openWires
        = (leftPad ++ (fSegment ++ gapSegment)) ++ (gSegment ++ suffixWires) := by
      rw [decomp, ← natListAppendAssoc fSegment gapSegment (gSegment ++ suffixWires),
        ← natListAppendAssoc leftPad (fSegment ++ gapSegment) (gSegment ++ suffixWires)]
    cases boolEitherTrueOfOrTrue alphaTurnback with
    | inr isCap =>
        obtain ⟨domTwoBeq, codZeroBeq⟩ := boolBothTrueOfAndTrue isCap
        have domTwo : fMid.length = 2 := of_decide_eq_true domTwoBeq
        have codZero : fHigh.length = 0 := of_decide_eq_true codZeroBeq
        obtain ⟨readLeftWire, readRightWire, segPair⟩ :=
          natListEqPairOfLengthTwo fSegment (fSegLen.trans domTwo)
        subst segPair
        have readLeftEq : natListGetAt state.openWires alphaLeft.length = readLeftWire := by
          rw [decomp, ← padLen]
          show natListGetAt (leftPad ++ ([readLeftWire, readRightWire]
              ++ (gapSegment ++ (gSegment ++ suffixWires)))) (leftPad.length + 0) = readLeftWire
          exact natListGetAt_appendAtLength leftPad _ 0
        have readRightEq : natListGetAt state.openWires (alphaLeft.length + 1)
            = readRightWire := by
          rw [decomp, ← padLen]
          exact natListGetAt_appendAtLength leftPad _ 1
        have prefixLenShifted : (leftPad ++ ([readLeftWire, readRightWire] ++ gapSegment)).length
            = (composePath alphaLeft (composePath fMid gapPath)).length := by
          rw [lengthAppend leftPad ([readLeftWire, readRightWire] ++ gapSegment),
            lengthAppend [readLeftWire, readRightWire] gapSegment,
            ModalityPath.length_composePath alphaLeft (composePath fMid gapPath),
            ModalityPath.length_composePath fMid gapPath, padLen, gapLen, domTwo]
          rfl
        have highLenShifted : (composePath alphaLeft (composePath fHigh gapPath)).length + 2
            = (composePath alphaLeft (composePath fMid gapPath)).length := by
          rw [ModalityPath.length_composePath alphaLeft (composePath fHigh gapPath),
            ModalityPath.length_composePath fHigh gapPath,
            ModalityPath.length_composePath alphaLeft (composePath fMid gapPath),
            ModalityPath.length_composePath fMid gapPath, domTwo, codZero, Nat.zero_add,
            Nat.add_assoc alphaLeft.length gapPath.length 2,
            Nat.add_comm gapPath.length 2]
        have capWindowShifted : alphaLeft.length + 2
            ≤ (leftPad ++ ([readLeftWire, readRightWire] ++ gapSegment)).length := by
          rw [lengthAppend leftPad ([readLeftWire, readRightWire] ++ gapSegment),
            lengthAppend [readLeftWire, readRightWire] gapSegment, ← padLen]
          exact Nat.add_le_add_left (Nat.le_add_right 2 gapSegment.length) leftPad.length
        obtain ⟨sigma, carrier, simulation⟩ :=
          arcCapAtomPastCellSwapSimCount cellBeta
            (composePath alphaLeft (composePath fHigh gapPath))
            (composePath alphaLeft (composePath fMid gapPath)) betaRight state
            (leftPad ++ ([readLeftWire, readRightWire] ++ gapSegment)) gSegment suffixWires
            alphaLeft.length wellFormed betaTurnback
            (by rw [decompShifted]) prefixLenShifted highLenShifted gSegLen capWindowShifted
            (by rw [readLeftEq]
                exact windowsDisjoint readLeftWire (List.Mem.head _))
            (by rw [readRightEq]
                exact windowsDisjoint readRightWire (List.Mem.tail _ (List.Mem.head _)))
        have alphaRunsRedex : runArcCell state alphaLeft alphaRightRedex
            (RawTwoCellExpr.gen genAlpha) = stepCapArc state alphaLeft.length :=
          stepArcAtom_eq_stepCapArc state
            (SpineAtom.mk _ _ alphaLeft fMid fHigh genAlpha alphaRightRedex) domTwo codZero
        have alphaRunsReduct : ∀ midState : ArcWireState,
            runArcCell midState alphaLeft alphaRightReduct (RawTwoCellExpr.gen genAlpha)
              = stepCapArc midState alphaLeft.length :=
          fun midState => stepArcAtom_eq_stepCapArc midState
            (SpineAtom.mk _ _ alphaLeft fMid fHigh genAlpha alphaRightReduct) domTwo codZero
        refine ⟨sigma, ?_, ?_⟩
        · rw [alphaRunsRedex]
          exact carrier
        · rw [alphaRunsRedex, alphaRunsReduct]
          exact simulation
    | inl isCup =>
        obtain ⟨domZeroBeq, codTwoBeq⟩ := boolBothTrueOfAndTrue isCup
        have domZero : fMid.length = 0 := of_decide_eq_true domZeroBeq
        have codTwo : fHigh.length = 2 := of_decide_eq_true codTwoBeq
        have prefixLenShifted : (leftPad ++ (fSegment ++ gapSegment)).length
            = (composePath alphaLeft (composePath fMid gapPath)).length := by
          rw [lengthAppend leftPad (fSegment ++ gapSegment),
            lengthAppend fSegment gapSegment,
            ModalityPath.length_composePath alphaLeft (composePath fMid gapPath),
            ModalityPath.length_composePath fMid gapPath, padLen, gapLen, fSegLen, domZero]
        have highLenShifted : (composePath alphaLeft (composePath fHigh gapPath)).length
            = (composePath alphaLeft (composePath fMid gapPath)).length + 2 := by
          rw [ModalityPath.length_composePath alphaLeft (composePath fHigh gapPath),
            ModalityPath.length_composePath fHigh gapPath,
            ModalityPath.length_composePath alphaLeft (composePath fMid gapPath),
            ModalityPath.length_composePath fMid gapPath, domZero, codTwo, Nat.zero_add,
            Nat.add_assoc alphaLeft.length gapPath.length 2,
            Nat.add_comm gapPath.length 2, ← Nat.add_assoc alphaLeft.length 2 gapPath.length,
            Nat.add_right_comm alphaLeft.length 2 gapPath.length]
        have cupWindowShifted : alphaLeft.length ≤ (leftPad ++ (fSegment ++ gapSegment)).length := by
          rw [lengthAppend leftPad (fSegment ++ gapSegment), ← padLen]
          exact Nat.le_add_right _ _
        obtain ⟨sigma, carrier, simulation⟩ :=
          arcCupAtomPastCellSwapSimCount cellBeta
            (composePath alphaLeft (composePath fHigh gapPath))
            (composePath alphaLeft (composePath fMid gapPath)) betaRight state
            (leftPad ++ (fSegment ++ gapSegment)) gSegment suffixWires alphaLeft.length
            wellFormed betaTurnback (by rw [decompShifted]) prefixLenShifted highLenShifted
            gSegLen cupWindowShifted
        have alphaRunsRedex : runArcCell state alphaLeft alphaRightRedex
            (RawTwoCellExpr.gen genAlpha) = stepCupArc state alphaLeft.length :=
          stepArcAtom_eq_stepCupArc state
            (SpineAtom.mk _ _ alphaLeft fMid fHigh genAlpha alphaRightRedex) domZero codTwo
        have alphaRunsReduct : ∀ midState : ArcWireState,
            runArcCell midState alphaLeft alphaRightReduct (RawTwoCellExpr.gen genAlpha)
              = stepCupArc midState alphaLeft.length :=
          fun midState => stepArcAtom_eq_stepCupArc midState
            (SpineAtom.mk _ _ alphaLeft fMid fHigh genAlpha alphaRightReduct) domZero codTwo
        refine ⟨sigma, ?_, ?_⟩
        · rw [alphaRunsRedex]
          exact carrier
        · rw [alphaRunsRedex, alphaRunsReduct]
          exact simulation
  | _, _, fMid, fHigh, @RawTwoCellExpr.vcomp _ _ _ _ fPipe _ alphaOne alphaTwo, _, _, _, _, cellBeta, alphaLeft, gapPath,
      alphaRightRedex, alphaRightReduct, betaRight, state, leftPad, fSegment, gapSegment,
      gSegment, suffixWires, wellFormed, alphaTurnback, betaTurnback, decomp, padLen, fSegLen,
      gapLen, gSegLen, windowsDisjoint => by
    obtain ⟨oneTurnback, twoTurnback⟩ := boolBothTrueOfAndTrue alphaTurnback
    obtain ⟨fPipeSegment, decompPipe, fPipeLen, probeFactsAlphaOne⟩ :=
      arcCellSegmentRun_ofWellFormed alphaOne alphaLeft alphaRightRedex state leftPad fSegment
        (gapSegment ++ (gSegment ++ suffixWires)) wellFormed oneTurnback decomp padLen fSegLen
    have wellFormedMid : WellFormedArcState
        (runArcCell state alphaLeft alphaRightRedex alphaOne) :=
      wellFormedArcState_runArcCell state alphaLeft alphaRightRedex alphaOne wellFormed
    have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
      fun edge edgeMem => (wellFormed.isFresh.2.1 edge edgeMem).2
    have windowsDisjointPipe : arcWindowsComponentDisjoint
        (runArcCell state alphaLeft alphaRightRedex alphaOne).links fPipeSegment gSegment := by
      intro fWire fWireMem gWire gWireMem
      have gWireMemState : gWire ∈ state.openWires := by
        rw [decomp]
        exact natListMem_appendOfRight leftPad _ (natListMem_appendOfRight fSegment _
          (natListMem_appendOfRight gapSegment _
            (natListMem_appendOfLeft gSegment suffixWires gWireMem)))
      have gWireRootBelow : unionFindRootOf state.links gWire < state.nextFresh :=
        unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow gWire
          (wellFormed.isFresh.1 gWire gWireMemState)
      have gWireGuard : arcProbeDisjointFromSegment state.links gWire fSegment :=
        fun fWireOld fWireOldMem =>
          isSameComponentFalse_symm (windowsDisjoint fWireOld fWireOldMem gWire gWireMem)
      obtain ⟨_, disjointPipe, _⟩ := probeFactsAlphaOne gWire gWireRootBelow gWireGuard
      exact isSameComponentFalse_symm (disjointPipe fWire fWireMem)
    obtain ⟨sigmaTwo, carrierTwo, simTwo⟩ :=
      arcCellPastCellSwapSimCount alphaTwo cellBeta alphaLeft gapPath alphaRightRedex
        alphaRightReduct betaRight (runArcCell state alphaLeft alphaRightRedex alphaOne)
        leftPad fPipeSegment gapSegment gSegment suffixWires wellFormedMid twoTurnback
        betaTurnback decompPipe padLen fPipeLen gapLen gSegLen windowsDisjointPipe
    obtain ⟨sigmaOne, carrierOne, simOne⟩ :=
      arcCellPastCellSwapSimCount alphaOne cellBeta alphaLeft gapPath alphaRightRedex
        alphaRightReduct betaRight state leftPad fSegment gapSegment gSegment suffixWires
        wellFormed oneTurnback betaTurnback decomp padLen fSegLen gapLen gSegLen windowsDisjoint
    have wellFormedSimOneRedex : WellFormedArcState
        (runArcCell (runArcCell state alphaLeft alphaRightRedex alphaOne)
          (composePath alphaLeft (composePath fPipe gapPath)) betaRight cellBeta) :=
      wellFormedArcState_runArcCell _ _ betaRight cellBeta wellFormedMid
    have wellFormedSimOneReduct : WellFormedArcState
        (runArcCell (runArcCell state (composePath alphaLeft (composePath fMid gapPath))
            betaRight cellBeta) alphaLeft alphaRightReduct alphaOne) :=
      wellFormedArcState_runArcCell _ alphaLeft alphaRightReduct alphaOne
        (wellFormedArcState_runArcCell state _ betaRight cellBeta wellFormed)
    obtain ⟨simExt, carrierExt⟩ := arcStepSimCount_extendByCommonCell sigmaOne state.nextFresh
      wellFormed.isNonDegenerate _ _ wellFormedSimOneRedex wellFormedSimOneReduct alphaLeft
      alphaRightReduct alphaTwo carrierOne simOne
    refine ⟨fun node => sigmaOne (sigmaTwo node), ?_, ?_⟩
    · rw [runArcCell_vcomp]
      exact arcBoundedSwapCarrier_comp
        (arcBoundedSwapCarrier_weaken carrierTwo
          (runArcCell_nextFresh_le state alphaLeft alphaRightRedex alphaOne) (Nat.le_refl _))
        (arcBoundedSwapCarrier_weaken carrierExt (Nat.le_refl _)
          (Nat.le_of_eq simTwo.nfEq.symm))
    · rw [runArcCell_vcomp, runArcCell_vcomp]
      exact arcStepSimCount_comp sigmaTwo sigmaOne _ _ _ simTwo simExt
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodyDom bodyCod body, _, _, _, _, cellBeta,
      alphaLeft, gapPath, alphaRightRedex, alphaRightReduct, betaRight, state, leftPad, fSegment,
      gapSegment, gSegment, suffixWires, wellFormed, alphaTurnback, betaTurnback, decomp, padLen,
      fSegLen, gapLen, gSegLen, windowsDisjoint => by
    have fLenSplit : fSegment.length = oneCell.length + bodyDom.length := by
      rw [fSegLen]
      exact ModalityPath.length_composePath oneCell bodyDom
    obtain ⟨oneSegment, bodyFSegment, segSplit, oneSegLen⟩ :=
      natListSplitAtLength fSegment oneCell.length
        (by rw [fLenSplit]; exact Nat.le_add_right _ _)
    have bodyFSegLen : bodyFSegment.length = bodyDom.length := by
      have totalLen : oneSegment.length + bodyFSegment.length
          = oneCell.length + bodyDom.length := by
        rw [← lengthAppend oneSegment bodyFSegment, ← segSplit]
        exact fLenSplit
      rw [oneSegLen] at totalLen
      exact natAddLeftCancelSeg oneCell.length _ _ totalLen
    have decompShifted : state.openWires = (leftPad ++ oneSegment)
        ++ (bodyFSegment ++ (gapSegment ++ (gSegment ++ suffixWires))) := by
      rw [decomp, segSplit,
        natListAppendAssoc oneSegment bodyFSegment (gapSegment ++ (gSegment ++ suffixWires)),
        ← natListAppendAssoc leftPad oneSegment
          (bodyFSegment ++ (gapSegment ++ (gSegment ++ suffixWires)))]
    have padLenShifted : (leftPad ++ oneSegment).length
        = (composePath alphaLeft oneCell).length := by
      rw [lengthAppend leftPad oneSegment,
        ModalityPath.length_composePath alphaLeft oneCell, padLen, oneSegLen]
    have highPathEq : composePath alphaLeft (composePath (composePath oneCell bodyCod) gapPath)
        = composePath (composePath alphaLeft oneCell) (composePath bodyCod gapPath) := by
      rw [composePath_assoc oneCell bodyCod gapPath,
        ← composePath_assoc alphaLeft oneCell (composePath bodyCod gapPath)]
    have midPathEq : composePath alphaLeft (composePath (composePath oneCell bodyDom) gapPath)
        = composePath (composePath alphaLeft oneCell) (composePath bodyDom gapPath) := by
      rw [composePath_assoc oneCell bodyDom gapPath,
        ← composePath_assoc alphaLeft oneCell (composePath bodyDom gapPath)]
    obtain ⟨sigma, carrier, simulation⟩ :=
      arcCellPastCellSwapSimCount body cellBeta (composePath alphaLeft oneCell) gapPath
        alphaRightRedex alphaRightReduct betaRight state (leftPad ++ oneSegment) bodyFSegment
        gapSegment gSegment suffixWires wellFormed alphaTurnback betaTurnback decompShifted
        padLenShifted bodyFSegLen gapLen gSegLen
        (fun fWire fWireMem => windowsDisjoint fWire
          (by rw [segSplit]; exact natListMem_appendOfRight oneSegment bodyFSegment fWireMem))
    rw [highPathEq, midPathEq]
    exact ⟨sigma, carrier, simulation⟩
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ bodyDom bodyCod oneCell body, _, _, _, _, cellBeta,
      alphaLeft, gapPath, alphaRightRedex, alphaRightReduct, betaRight, state, leftPad, fSegment,
      gapSegment, gSegment, suffixWires, wellFormed, alphaTurnback, betaTurnback, decomp, padLen,
      fSegLen, gapLen, gSegLen, windowsDisjoint => by
    have fLenSplit : fSegment.length = bodyDom.length + oneCell.length := by
      rw [fSegLen]
      exact ModalityPath.length_composePath bodyDom oneCell
    obtain ⟨bodyFSegment, oneSegment, segSplit, bodyFSegLen⟩ :=
      natListSplitAtLength fSegment bodyDom.length
        (by rw [fLenSplit]; exact Nat.le_add_right _ _)
    have oneSegLen : oneSegment.length = oneCell.length := by
      have totalLen : bodyFSegment.length + oneSegment.length
          = bodyDom.length + oneCell.length := by
        rw [← lengthAppend bodyFSegment oneSegment, ← segSplit]
        exact fLenSplit
      rw [bodyFSegLen] at totalLen
      exact natAddLeftCancelSeg bodyDom.length _ _ totalLen
    have decompShifted : state.openWires = leftPad
        ++ (bodyFSegment ++ ((oneSegment ++ gapSegment) ++ (gSegment ++ suffixWires))) := by
      rw [decomp, segSplit,
        natListAppendAssoc bodyFSegment oneSegment (gapSegment ++ (gSegment ++ suffixWires)),
        ← natListAppendAssoc oneSegment gapSegment (gSegment ++ suffixWires)]
    have gapLenShifted : (oneSegment ++ gapSegment).length
        = (composePath oneCell gapPath).length := by
      rw [lengthAppend oneSegment gapSegment,
        ModalityPath.length_composePath oneCell gapPath, oneSegLen, gapLen]
    have highPathEq : composePath alphaLeft (composePath (composePath bodyCod oneCell) gapPath)
        = composePath alphaLeft (composePath bodyCod (composePath oneCell gapPath)) := by
      rw [composePath_assoc bodyCod oneCell gapPath]
    have midPathEq : composePath alphaLeft (composePath (composePath bodyDom oneCell) gapPath)
        = composePath alphaLeft (composePath bodyDom (composePath oneCell gapPath)) := by
      rw [composePath_assoc bodyDom oneCell gapPath]
    obtain ⟨sigma, carrier, simulation⟩ :=
      arcCellPastCellSwapSimCount body cellBeta alphaLeft (composePath oneCell gapPath)
        (composePath oneCell alphaRightRedex) (composePath oneCell alphaRightReduct) betaRight
        state leftPad bodyFSegment (oneSegment ++ gapSegment) gSegment suffixWires wellFormed
        alphaTurnback betaTurnback decompShifted padLen bodyFSegLen gapLenShifted gSegLen
        (fun fWire fWireMem => windowsDisjoint fWire
          (by rw [segSplit]; exact natListMem_appendOfLeft bodyFSegment oneSegment fWireMem))
    rw [highPathEq, midPathEq]
    exact ⟨sigma, carrier, simulation⟩

/-! ## Fires — whole cell past whole cell, machine-instantiated -/

/-- ★★ **`cellPastCell` FIRED: the THREE-atom cell past the THREE-atom cell** (six atoms total,
both orders, gap zero): two copies of the cup/cup/cap fixture in the Godement configuration from
the two-wire seed.  Every guard is vacuous (both dom windows empty), the whole content is the
double induction. -/
theorem arcThreeAtomCellPastThreeAtomCell_fired :
    ∃ sigma,
      ArcBoundedSwapCarrier arcCupPastCellFireSeed.nextFresh
          (runArcCell (runArcCell arcCupPastCellFireSeed adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell)
            (composePath adjunctionLeftThenRight (composePath adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)))
            (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
            threeAtomTurnbackCell).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (runArcCell arcCupPastCellFireSeed adjunctionLeftThenRight
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                threeAtomTurnbackCell)
              (composePath adjunctionLeftThenRight (composePath adjunctionLeftThenRight
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)))
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell)
            (runArcCell (runArcCell arcCupPastCellFireSeed
                (composePath adjunctionLeftThenRight (composePath
                  (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                  (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)))
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                threeAtomTurnbackCell)
              adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell) :=
  arcCellPastCellSwapSimCount threeAtomTurnbackCell threeAtomTurnbackCell
    adjunctionLeftThenRight
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    arcCupPastCellFireSeed [0, 1] [] [] [] [] arcCupPastCellFireSeed_isWellFormed
    threeAtomTurnbackCell_isTurnbackOnly threeAtomTurnbackCell_isTurnbackOnly rfl rfl rfl rfl rfl
    (fun _ fWireMem => nomatch fWireMem)

/-- The six-wire seed for the cap-bearing alpha fire. -/
def arcCellPastCellCapFireSeed : ArcWireState := ArcWireState.mk [0, 1, 2, 3, 4, 5] [] 6 0 [] []

/-- The six-wire seed is well-formed. -/
theorem arcCellPastCellCapFireSeed_isWellFormed : WellFormedArcState arcCellPastCellCapFireSeed :=
  ⟨by unfold ArcStateFresh arcCellPastCellCapFireSeed; decide, trivial, by decide⟩

/-- ★★ **`cellPastCell` FIRED with a CAP-bearing alpha on real wires**: the whisker-sandwiched
counit cell (dom `[l,r,l,r]`, four live wires `[2,3,4,5]`) past the three-atom cell, from the
six-wire seed — the f-window is nonempty, so the alpha side consumes genuine cap reads. -/
theorem arcCounitCellPastThreeAtomCell_fired :
    ∃ sigma,
      ArcBoundedSwapCarrier arcCellPastCellCapFireSeed.nextFresh
          (runArcCell (runArcCell arcCellPastCellCapFireSeed adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              whiskerSandwichedCounitCell)
            (composePath adjunctionLeftThenRight (composePath adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)))
            (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
            threeAtomTurnbackCell).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (runArcCell arcCellPastCellCapFireSeed adjunctionLeftThenRight
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                whiskerSandwichedCounitCell)
              (composePath adjunctionLeftThenRight (composePath adjunctionLeftThenRight
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)))
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              threeAtomTurnbackCell)
            (runArcCell (runArcCell arcCellPastCellCapFireSeed
                (composePath adjunctionLeftThenRight (composePath
                  (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
                  (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)))
                (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
                threeAtomTurnbackCell)
              adjunctionLeftThenRight
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
              whiskerSandwichedCounitCell) :=
  arcCellPastCellSwapSimCount whiskerSandwichedCounitCell threeAtomTurnbackCell
    adjunctionLeftThenRight
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    arcCellPastCellCapFireSeed [0, 1] [2, 3, 4, 5] [] [] []
    arcCellPastCellCapFireSeed_isWellFormed rfl threeAtomTurnbackCell_isTurnbackOnly rfl rfl rfl
    rfl rfl (fun _ _ _ gWireMem => nomatch gWireMem)

/-! ## Honesty marker + pins -/

/-- **Honesty marker — `cellPastCell` is SHIPPED: the whole-cell disjoint-support commutation
theorem is genuinely inhabited.**  A whole turnback-only cell commutes past a whole turnback-only
cell over the bundle, under the two-window component-disjointness invariant, with a bounded
composite carrier; the double induction (alpha side here, beta side in Brick 2) is closed; fired
on three-atom-past-three-atom and cap-bearing instances.  `= true`. -/
def fxMode_hasArcCellPastCellSwapSimCount : Bool := true

/-- **Honesty pin — the `:234` whisker-support pin stays `false`:** its VERBATIM demand is the
order-sensitive links-LIST equality `reduct.links = renameLinks sigma redex.links`, a DIFFERENT
statement shape from this brick's order-insensitive `ArcStepSimCount` (Brick 4 adjudicates the
list shape).  `rfl`. -/
theorem arcCellPastCell_disjointWhiskerSupport_stays_false :
    fxMode_hasDisjointWhiskerSupport = false := rfl

/-- **Honesty pin — `:3046` residual (2) stays OPEN as stated:** `ArcGodementCoreSwapSimCount`
demands the existential over ARBITRARY well-formed states (no window decomposition, no
component-disjointness hypothesis) and over cells with BOX atoms; this brick delivers the
guarded turnback-only core.  `rfl`. -/
theorem arcCellPastCell_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

/-- **Honesty pin — the partition-commute keystone stays OPEN** (refuted as stated).  `rfl`. -/
theorem arcCellPastCell_partitionCommute_stays_false :
    fxMode_hasArcPartitionCommuteProof = false := rfl

/-- **Honesty pin — the machine-refuted same-partition-fresh keystone is NEVER flipped.**  `rfl`. -/
theorem arcCellPastCell_samePartitionFresh_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
