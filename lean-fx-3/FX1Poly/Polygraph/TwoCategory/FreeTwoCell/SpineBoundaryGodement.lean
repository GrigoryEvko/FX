import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement

/-! # mode-3 — boundary chains across the Godement step (the in-range extraction kit)

`SpineBoundaryChain` shipped the chain discipline; this file works it across the interchange.
For the Godement redex/reduct nests (the two transposed four-cell spine difference-lists of
`SpineGodementStep`):

  * `crossLayerBoundaryEq` — the one boundary-form conversion the nests need: an f-layer
    boundary (`leftAcc + f + (g ++ rightAcc)`) equals the corresponding g-layer boundary
    (`(leftAcc ++ f) + g + rightAcc`);
  * `spineBoundaryChained_interchangeRedex_entryPinned` /
    `spineBoundaryChained_interchangeReduct_entryPinned` — the ENTRY DICHOTOMY: a chained
    nest either pins the chain boundary to the redex's entry width (its first
    generator-carrying cell fires at the entry, with generator-free prefixes contributing
    boundary-silent path equalities), or ALL FOUR cells are generator-free and both nests
    collapse to the shared tail;
  * `…Redex_exit` / `…Reduct_exit` (peel) and `…Redex_ofExit` / `…Reduct_ofExit` (build) —
    at a pinned entry, chainedness of either nest is equivalent to chainedness of the tail
    at the COMMON exit width `(leftAcc ++ fHigh) + gHigh + rightAcc`;
  * `SpineGodementStep.preservesBoundaryChained` / `.reflectsBoundaryChained` — the Godement
    step preserves boundary chains in both directions (peel one nest, rebuild the other);
  * `SpineTraceEquiv.boundaryChainedIff` — full trace equivalence preserves boundary chains
    at every boundary (induction with the biconditional motive; `consCongr` re-chains the
    shared head);
  * `interchangeWindow_le_ofEntryPinned` — the pinned entry yields the in-range read premise
    `leftAcc + fLow + gLow ≤ boundaryLength` that
    `matchingGodementComponentCoreSwap_ofInRange` consumes.

What remains for MODE3-B after this brick: relate `state.openWires.length` to the chain
boundary through `stepAtom` (the state-side count invariant), thread both through the
conditioned trace induction, and handle the empty-boundary degeneracy — then re-seat the
soundness capstone.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat successor disequality (hand-rolled; core `Nat.succ_ne_zero` leaks `propext`) -/

private theorem natSuccNeZero (anyNat : Nat) : Nat.succ anyNat ≠ 0 := fun succEqZero =>
  Nat.noConfusion succEqZero

/-! ## The cross-layer boundary conversion -/

/-- The one boundary-form conversion the interchange nests need: the f-layer reading of a
four-segment boundary (`leftAcc + first + (second ++ rightAcc)`) equals its g-layer reading
(`(leftAcc ++ first) + second + rightAcc`). -/
theorem crossLayerBoundaryEq {graph : ModeGraph}
    {overallSource sourceMode middleMode targetMode overallTarget : graph.Mode}
    (leftAccumulator : ModalityPath graph overallSource sourceMode)
    (firstPath : ModalityPath graph sourceMode middleMode)
    (secondPath : ModalityPath graph middleMode targetMode)
    (rightAccumulator : ModalityPath graph targetMode overallTarget) :
    leftAccumulator.length + firstPath.length
        + (composePath secondPath rightAccumulator).length
      = (composePath leftAccumulator firstPath).length + secondPath.length
        + rightAccumulator.length := by
  rw [ModalityPath.length_composePath secondPath rightAccumulator,
    ModalityPath.length_composePath leftAccumulator firstPath]
  exact (Nat.add_assoc (leftAccumulator.length + firstPath.length) secondPath.length
    rightAccumulator.length).symm

/-! ## The entry dichotomy -/

/-- **Entry dichotomy for the interchange REDEX nest.**  A chained redex nest either PINS the
chain boundary to the entry width `leftAcc + fLow + (gLow ++ rightAcc)` — its first
generator-carrying cell fires at the entry, and the generator-free prefix cells contribute
boundary-silent path equalities — or all four cells are generator-free and BOTH nests collapse
to the shared tail. -/
theorem spineBoundaryChained_interchangeRedex_entryPinned {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    {boundaryLength : Nat}
    (chained : SpineBoundaryChained boundaryLength
      (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
        (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc)
          (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc
            (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))))) :
    leftAcc.length + fLow.length + (composePath gLow rightAcc).length = boundaryLength
      ∨ (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
            (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc)
              (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc
                (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))) = rest
          ∧ cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
              (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc
                (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc)
                  (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest)))
            = rest) := by
  cases alphaProbe : cellAlpha.generatorCount with
  | succ alphaPredecessor =>
      exact Or.inl (spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero leftAcc
        (composePath gLow rightAcc) cellAlpha _
        (fun alphaZero => absurd (alphaProbe.symm.trans alphaZero)
          (natSuccNeZero alphaPredecessor))
        chained)
  | zero =>
      have alphaSilent := RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero
        cellAlpha alphaProbe
      rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
        (composePath gLow rightAcc) cellAlpha _ alphaProbe] at chained
      cases alphaUpperProbe : cellAlphaUpper.generatorCount with
      | succ alphaUpperPredecessor =>
          have pinned := spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero leftAcc
            (composePath gLow rightAcc) cellAlphaUpper _
            (fun alphaUpperZero => absurd (alphaUpperProbe.symm.trans alphaUpperZero)
              (natSuccNeZero alphaUpperPredecessor))
            chained
          refine Or.inl ?_
          rw [alphaSilent]
          exact pinned
      | zero =>
          have alphaUpperSilent :=
            RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero cellAlphaUpper
              alphaUpperProbe
          rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
            (composePath gLow rightAcc) cellAlphaUpper _ alphaUpperProbe] at chained
          cases betaProbe : cellBeta.generatorCount with
          | succ betaPredecessor =>
              have pinned := spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
                (composePath leftAcc fHigh) rightAcc cellBeta _
                (fun betaZero => absurd (betaProbe.symm.trans betaZero)
                  (natSuccNeZero betaPredecessor))
                chained
              refine Or.inl ?_
              rw [alphaSilent, alphaUpperSilent,
                crossLayerBoundaryEq leftAcc fHigh gLow rightAcc]
              exact pinned
          | zero =>
              have betaSilent :=
                RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero cellBeta
                  betaProbe
              rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                (composePath leftAcc fHigh) rightAcc cellBeta _ betaProbe] at chained
              cases betaUpperProbe : cellBetaUpper.generatorCount with
              | succ betaUpperPredecessor =>
                  have pinned :=
                    spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
                      (composePath leftAcc fHigh) rightAcc cellBetaUpper rest
                      (fun betaUpperZero => absurd (betaUpperProbe.symm.trans betaUpperZero)
                        (natSuccNeZero betaUpperPredecessor))
                      chained
                  refine Or.inl ?_
                  rw [alphaSilent, alphaUpperSilent, betaSilent,
                    crossLayerBoundaryEq leftAcc fHigh gMid rightAcc]
                  exact pinned
              | zero =>
                  refine Or.inr ⟨?_, ?_⟩
                  · rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gLow rightAcc) cellAlpha _ alphaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gLow rightAcc) cellAlphaUpper _ alphaUpperProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fHigh) rightAcc cellBeta _ betaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fHigh) rightAcc cellBetaUpper rest
                        betaUpperProbe]
                  · rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gLow rightAcc) cellAlpha _ alphaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fMid) rightAcc cellBeta _ betaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gMid rightAcc) cellAlphaUpper _ alphaUpperProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fHigh) rightAcc cellBetaUpper rest
                        betaUpperProbe]

/-- **Entry dichotomy for the interchange REDUCT nest** — same disjunction as the redex side,
read off the transposed layer order (`cellAlpha`, then `cellBeta` at `leftAcc ++ fMid`, then
`cellAlphaUpper` at `gMid ++ rightAcc`, then `cellBetaUpper`). -/
theorem spineBoundaryChained_interchangeReduct_entryPinned {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    {boundaryLength : Nat}
    (chained : SpineBoundaryChained boundaryLength
      (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
        (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc
          (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc)
            (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))))) :
    leftAcc.length + fLow.length + (composePath gLow rightAcc).length = boundaryLength
      ∨ (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
            (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc)
              (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc
                (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest))) = rest
          ∧ cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
              (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc
                (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc)
                  (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest)))
            = rest) := by
  cases alphaProbe : cellAlpha.generatorCount with
  | succ alphaPredecessor =>
      exact Or.inl (spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero leftAcc
        (composePath gLow rightAcc) cellAlpha _
        (fun alphaZero => absurd (alphaProbe.symm.trans alphaZero)
          (natSuccNeZero alphaPredecessor))
        chained)
  | zero =>
      have alphaSilent := RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero
        cellAlpha alphaProbe
      rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
        (composePath gLow rightAcc) cellAlpha _ alphaProbe] at chained
      cases betaProbe : cellBeta.generatorCount with
      | succ betaPredecessor =>
          have pinned := spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
            (composePath leftAcc fMid) rightAcc cellBeta _
            (fun betaZero => absurd (betaProbe.symm.trans betaZero)
              (natSuccNeZero betaPredecessor))
            chained
          refine Or.inl ?_
          rw [alphaSilent, crossLayerBoundaryEq leftAcc fMid gLow rightAcc]
          exact pinned
      | zero =>
          have betaSilent := RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero
            cellBeta betaProbe
          rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
            (composePath leftAcc fMid) rightAcc cellBeta _ betaProbe] at chained
          cases alphaUpperProbe : cellAlphaUpper.generatorCount with
          | succ alphaUpperPredecessor =>
              have pinned := spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
                leftAcc (composePath gMid rightAcc) cellAlphaUpper _
                (fun alphaUpperZero => absurd (alphaUpperProbe.symm.trans alphaUpperZero)
                  (natSuccNeZero alphaUpperPredecessor))
                chained
              refine Or.inl ?_
              rw [alphaSilent, betaSilent]
              exact pinned
          | zero =>
              have alphaUpperSilent :=
                RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero cellAlphaUpper
                  alphaUpperProbe
              rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                (composePath gMid rightAcc) cellAlphaUpper _ alphaUpperProbe] at chained
              cases betaUpperProbe : cellBetaUpper.generatorCount with
              | succ betaUpperPredecessor =>
                  have pinned :=
                    spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
                      (composePath leftAcc fHigh) rightAcc cellBetaUpper rest
                      (fun betaUpperZero => absurd (betaUpperProbe.symm.trans betaUpperZero)
                        (natSuccNeZero betaUpperPredecessor))
                      chained
                  refine Or.inl ?_
                  rw [alphaSilent, alphaUpperSilent, betaSilent,
                    crossLayerBoundaryEq leftAcc fHigh gMid rightAcc]
                  exact pinned
              | zero =>
                  refine Or.inr ⟨?_, ?_⟩
                  · rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gLow rightAcc) cellAlpha _ alphaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gLow rightAcc) cellAlphaUpper _ alphaUpperProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fHigh) rightAcc cellBeta _ betaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fHigh) rightAcc cellBetaUpper rest
                        betaUpperProbe]
                  · rw [RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gLow rightAcc) cellAlpha _ alphaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fMid) rightAcc cellBeta _ betaProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero leftAcc
                        (composePath gMid rightAcc) cellAlphaUpper _ alphaUpperProbe,
                      RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
                        (composePath leftAcc fHigh) rightAcc cellBetaUpper rest
                        betaUpperProbe]

/-! ## Peel and build: chainedness of a nest at pinned entry = chainedness of the tail at exit -/

/-- **Peel the REDEX nest.**  At a pinned entry, the tail is chained at the common exit width
`(leftAcc ++ fHigh) + gHigh + rightAcc`. -/
theorem spineBoundaryChained_interchangeRedex_exit {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    {boundaryLength : Nat}
    (chained : SpineBoundaryChained boundaryLength
      (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
        (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc)
          (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc
            (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest)))))
    (entryPinned : leftAcc.length + fLow.length + (composePath gLow rightAcc).length
      = boundaryLength) :
    SpineBoundaryChained
      ((composePath leftAcc fHigh).length + gHigh.length + rightAcc.length) rest := by
  rw [← entryPinned] at chained
  have chainedAlphaUpper := spineBoundaryChained_rest_of_spineDiff leftAcc
    (composePath gLow rightAcc) cellAlpha _ chained
  have chainedBeta := spineBoundaryChained_rest_of_spineDiff leftAcc
    (composePath gLow rightAcc) cellAlphaUpper _ chainedAlphaUpper
  rw [crossLayerBoundaryEq leftAcc fHigh gLow rightAcc] at chainedBeta
  have chainedBetaUpper := spineBoundaryChained_rest_of_spineDiff (composePath leftAcc fHigh)
    rightAcc cellBeta _ chainedBeta
  exact spineBoundaryChained_rest_of_spineDiff (composePath leftAcc fHigh) rightAcc
    cellBetaUpper rest chainedBetaUpper

/-- **Build the REDEX nest.**  From a tail chained at the exit width, the redex nest is
chained at the entry width. -/
theorem spineBoundaryChained_interchangeRedex_ofExit {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (exitChained : SpineBoundaryChained
      ((composePath leftAcc fHigh).length + gHigh.length + rightAcc.length) rest) :
    SpineBoundaryChained
      (leftAcc.length + fLow.length + (composePath gLow rightAcc).length)
      (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
        (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc)
          (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc
            (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest)))) := by
  have builtBetaUpper := spineBoundaryChained_spineDiff (composePath leftAcc fHigh) rightAcc
    cellBetaUpper rest exitChained
  have builtBeta := spineBoundaryChained_spineDiff (composePath leftAcc fHigh) rightAcc
    cellBeta _ builtBetaUpper
  rw [← crossLayerBoundaryEq leftAcc fHigh gLow rightAcc] at builtBeta
  have builtAlphaUpper := spineBoundaryChained_spineDiff leftAcc (composePath gLow rightAcc)
    cellAlphaUpper _ builtBeta
  exact spineBoundaryChained_spineDiff leftAcc (composePath gLow rightAcc) cellAlpha _
    builtAlphaUpper

/-- **Peel the REDUCT nest.**  At a pinned entry, the tail is chained at the same exit width
as the redex side. -/
theorem spineBoundaryChained_interchangeReduct_exit {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    {boundaryLength : Nat}
    (chained : SpineBoundaryChained boundaryLength
      (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
        (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc
          (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc)
            (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest)))))
    (entryPinned : leftAcc.length + fLow.length + (composePath gLow rightAcc).length
      = boundaryLength) :
    SpineBoundaryChained
      ((composePath leftAcc fHigh).length + gHigh.length + rightAcc.length) rest := by
  rw [← entryPinned] at chained
  have chainedBeta := spineBoundaryChained_rest_of_spineDiff leftAcc
    (composePath gLow rightAcc) cellAlpha _ chained
  rw [crossLayerBoundaryEq leftAcc fMid gLow rightAcc] at chainedBeta
  have chainedAlphaUpper := spineBoundaryChained_rest_of_spineDiff (composePath leftAcc fMid)
    rightAcc cellBeta _ chainedBeta
  rw [← crossLayerBoundaryEq leftAcc fMid gMid rightAcc] at chainedAlphaUpper
  have chainedBetaUpper := spineBoundaryChained_rest_of_spineDiff leftAcc
    (composePath gMid rightAcc) cellAlphaUpper _ chainedAlphaUpper
  rw [crossLayerBoundaryEq leftAcc fHigh gMid rightAcc] at chainedBetaUpper
  exact spineBoundaryChained_rest_of_spineDiff (composePath leftAcc fHigh) rightAcc
    cellBetaUpper rest chainedBetaUpper

/-- **Build the REDUCT nest.**  From a tail chained at the exit width, the reduct nest is
chained at the entry width. -/
theorem spineBoundaryChained_interchangeReduct_ofExit {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (exitChained : SpineBoundaryChained
      ((composePath leftAcc fHigh).length + gHigh.length + rightAcc.length) rest) :
    SpineBoundaryChained
      (leftAcc.length + fLow.length + (composePath gLow rightAcc).length)
      (cellAlpha.spineDiff leftAcc (composePath gLow rightAcc)
        (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc
          (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc)
            (cellBetaUpper.spineDiff (composePath leftAcc fHigh) rightAcc rest)))) := by
  have builtBetaUpper := spineBoundaryChained_spineDiff (composePath leftAcc fHigh) rightAcc
    cellBetaUpper rest exitChained
  rw [← crossLayerBoundaryEq leftAcc fHigh gMid rightAcc] at builtBetaUpper
  have builtAlphaUpper := spineBoundaryChained_spineDiff leftAcc (composePath gMid rightAcc)
    cellAlphaUpper _ builtBetaUpper
  rw [crossLayerBoundaryEq leftAcc fMid gMid rightAcc] at builtAlphaUpper
  have builtBeta := spineBoundaryChained_spineDiff (composePath leftAcc fMid) rightAcc
    cellBeta _ builtAlphaUpper
  rw [← crossLayerBoundaryEq leftAcc fMid gLow rightAcc] at builtBeta
  exact spineBoundaryChained_spineDiff leftAcc (composePath gLow rightAcc) cellAlpha _
    builtBeta

/-! ## The Godement step preserves boundary chains, both ways -/

/-- The Godement step PRESERVES boundary chains: peel the redex at its pinned entry, rebuild
the reduct; if all four cells are generator-free, both nests are the shared tail. -/
theorem SpineGodementStep.preservesBoundaryChained {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList)
    {boundaryLength : Nat}
    (chained : SpineBoundaryChained boundaryLength firstList) :
    SpineBoundaryChained boundaryLength secondList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
      cases spineBoundaryChained_interchangeRedex_entryPinned cellAlpha cellAlphaUpper
          cellBeta cellBetaUpper leftAcc rightAcc rest chained with
      | inl entryPinned =>
          exact entryPinned ▸ spineBoundaryChained_interchangeReduct_ofExit cellAlpha
            cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
            (spineBoundaryChained_interchangeRedex_exit cellAlpha cellAlphaUpper cellBeta
              cellBetaUpper leftAcc rightAcc rest chained entryPinned)
      | inr bothCollapse =>
          rw [bothCollapse.2]
          rw [bothCollapse.1] at chained
          exact chained

/-- The Godement step REFLECTS boundary chains: peel the reduct at its pinned entry, rebuild
the redex. -/
theorem SpineGodementStep.reflectsBoundaryChained {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList)
    {boundaryLength : Nat}
    (chained : SpineBoundaryChained boundaryLength secondList) :
    SpineBoundaryChained boundaryLength firstList := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
      cases spineBoundaryChained_interchangeReduct_entryPinned cellAlpha cellAlphaUpper
          cellBeta cellBetaUpper leftAcc rightAcc rest chained with
      | inl entryPinned =>
          exact entryPinned ▸ spineBoundaryChained_interchangeRedex_ofExit cellAlpha
            cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
            (spineBoundaryChained_interchangeReduct_exit cellAlpha cellAlphaUpper cellBeta
              cellBetaUpper leftAcc rightAcc rest chained entryPinned)
      | inr bothCollapse =>
          rw [bothCollapse.1]
          rw [bothCollapse.2] at chained
          exact chained

/-- ★ **Trace equivalence preserves boundary chains at every boundary** — the biconditional
motive threads `symm`/`trans` for free, the Godement step contributes both directions, and
`consCongr` re-chains the shared head at its target boundary. -/
theorem SpineTraceEquiv.boundaryChainedIff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ (boundaryLength : Nat),
      SpineBoundaryChained boundaryLength firstList
        ↔ SpineBoundaryChained boundaryLength secondList := by
  induction equiv with
  | ofStep step =>
      exact fun boundaryLength =>
        ⟨step.preservesBoundaryChained, step.reflectsBoundaryChained⟩
  | refl _ => exact fun _ => Iff.rfl
  | symm _ innerIff => exact fun boundaryLength => (innerIff boundaryLength).symm
  | trans _ _ leftIff rightIff =>
      exact fun boundaryLength => (leftIff boundaryLength).trans (rightIff boundaryLength)
  | consCongr atom _ tailIff =>
      intro boundaryLength
      constructor
      · intro chainedFirst
        have headAndTail := spineBoundaryChained_tail chainedFirst
        exact SpineBoundaryChained.cons atom headAndTail.1
          ((tailIff atom.codBoundaryLength).mp headAndTail.2)
      · intro chainedSecond
        have headAndTail := spineBoundaryChained_tail chainedSecond
        exact SpineBoundaryChained.cons atom headAndTail.1
          ((tailIff atom.codBoundaryLength).mpr headAndTail.2)

/-! ## The in-range read premise from a pinned entry -/

/-- A pinned entry yields the IN-RANGE read premise the discharged component core swap
consumes: the Godement window `leftAcc + fLow + gLow` fits inside the chain boundary (the
right accumulator is the slack). -/
theorem interchangeWindow_le_ofEntryPinned {graph : ModeGraph}
    {overallSource sourceMode middleMode targetMode overallTarget : graph.Mode}
    (leftAcc : ModalityPath graph overallSource sourceMode)
    (fLow : ModalityPath graph sourceMode middleMode)
    (gLow : ModalityPath graph middleMode targetMode)
    (rightAcc : ModalityPath graph targetMode overallTarget)
    {boundaryLength : Nat}
    (entryPinned : leftAcc.length + fLow.length + (composePath gLow rightAcc).length
      = boundaryLength) :
    leftAcc.length + fLow.length + gLow.length ≤ boundaryLength := by
  rw [← entryPinned, ModalityPath.length_composePath gLow rightAcc,
    ← Nat.add_assoc (leftAcc.length + fLow.length) gLow.length rightAcc.length]
  exact Nat.le_add_right (leftAcc.length + fLow.length + gLow.length) rightAcc.length

/-! ## Honesty marker -/

/-- **Honesty marker — the Godement-nest boundary kit is SHIPPED.**  Entry dichotomies for
both interchange nests (`…Redex_entryPinned` / `…Reduct_entryPinned`), peel/build between the
pinned entry and the common exit for both nests, step preservation/reflection
(`SpineGodementStep.preservesBoundaryChained` / `.reflectsBoundaryChained`), full
trace-equivalence invariance (`SpineTraceEquiv.boundaryChainedIff`), and the in-range window
bound (`interchangeWindow_le_ofEntryPinned`).  NOT yet covered: relating
`state.openWires.length` to the chain boundary through `stepAtom` and threading both through
the conditioned trace induction to discharge the unconditional core swap (plus the
empty-boundary degeneracy) — the next brick.  `= true`. -/
def fxMode_hasSpineBoundaryGodementKit : Bool := true

end FX1Poly.Polygraph
