import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicMove

/-! # AtomicSwapGeneration — atom swaps generate the trace equivalence (FREE-5 closure)

The generation theorem: the block-level Godement step is INSIDE the atomic swap closure, so
`SpineTraceEquiv = AtomicTraceEquiv` and the trace decision may work at atom granularity.

  * `AtomicTraceEquiv.blockMovePastCell` — the atom move lemma iterated over the moving
    block: an ARBITRARY cell's spine block moves past an arbitrary passive block, by
    structural recursion on the MOVING cell this time (`gen` = the atom move, `id` = refl,
    `vcomp` = two moves under a `prependSpineDiff`, whiskers = recursion with the whiskering
    1-cell absorbed into the left accumulator / the inert zone + reassociation transports);
  * `SpineGodementStep.toAtomicTraceEquiv` — the Godement step IS a block move at
    `inertPath := identityPath` under the shared `cellAlpha` prefix (the two identity-path
    laws bridge the inert-zone spellings);
  * `SpineTraceEquiv.toAtomicTraceEquiv` + `spineTraceEquiv_iff_atomicTraceEquiv` — the two
    closures coincide (the other inclusion is `AtomicTraceEquiv.toSpineTraceEquiv`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The block move**: an arbitrary moving cell's spine block, separated by an inert zone
from an arbitrary passive cell's spine block, moves past it inside the atomic swap closure —
`moveGeneratorPastCell` iterated over the moving block by structural recursion on the moving
cell. -/
theorem AtomicTraceEquiv.blockMovePastCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {betaSource betaTarget : signature.graph.Mode}
    {betaDom betaCod : ModalityPath signature.graph betaSource betaTarget}
    (cellBeta : RawTwoCellExpr signature betaDom betaCod)
    (rightAcc : ModalityPath signature.graph betaTarget overallTarget) :
    {swapSourceMode swapMiddleLeft : signature.graph.Mode} →
    {oneCellFMid oneCellFHigh : ModalityPath signature.graph swapSourceMode swapMiddleLeft} →
    (cellMoving : RawTwoCellExpr signature oneCellFMid oneCellFHigh) →
    (leftAcc : ModalityPath signature.graph overallSource swapSourceMode) →
    (inertPath : ModalityPath signature.graph swapMiddleLeft betaSource) →
    (tailAtoms : List (SpineAtom signature overallSource overallTarget)) →
    AtomicTraceEquiv signature
      (cellMoving.spineDiff leftAcc (composePath (composePath inertPath betaDom) rightAcc)
        (cellBeta.spineDiff (composePath (composePath leftAcc oneCellFHigh) inertPath)
          rightAcc tailAtoms))
      (cellBeta.spineDiff (composePath (composePath leftAcc oneCellFMid) inertPath) rightAcc
        (cellMoving.spineDiff leftAcc (composePath (composePath inertPath betaCod) rightAcc)
          tailAtoms))
  | _, _, _, _, .gen movingGenerator, leftAcc, inertPath, tailAtoms =>
      AtomicTraceEquiv.moveGeneratorPastCell movingGenerator leftAcc inertPath cellBeta
        rightAcc tailAtoms
  | _, _, _, _, .id sharedBoundary, leftAcc, inertPath, tailAtoms =>
      AtomicTraceEquiv.refl _
  | _, _, _, _, .vcomp cellLower cellUpper, leftAcc, inertPath, tailAtoms =>
      AtomicTraceEquiv.trans
        (AtomicTraceEquiv.prependSpineDiff leftAcc
          (composePath (composePath inertPath betaDom) rightAcc) cellLower
          (AtomicTraceEquiv.blockMovePastCell cellBeta rightAcc cellUpper leftAcc inertPath
            tailAtoms))
        (AtomicTraceEquiv.blockMovePastCell cellBeta rightAcc cellLower leftAcc inertPath
          (cellUpper.spineDiff leftAcc
            (composePath (composePath inertPath betaCod) rightAcc) tailAtoms))
  | _, _, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ whiskerCell bodyDom bodyCod body, leftAcc,
      inertPath, tailAtoms => by
      have inner := AtomicTraceEquiv.blockMovePastCell cellBeta rightAcc body
        (composePath leftAcc whiskerCell) inertPath tailAtoms
      rw [composePath_assoc leftAcc whiskerCell bodyCod,
        composePath_assoc leftAcc whiskerCell bodyDom] at inner
      exact inner
  | _, _, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ bodyDom bodyCod whiskerCell body, leftAcc,
      inertPath, tailAtoms => by
      have inner := AtomicTraceEquiv.blockMovePastCell cellBeta rightAcc body leftAcc
        (composePath whiskerCell inertPath) tailAtoms
      have reassocMovingDom : composePath
            (composePath (composePath whiskerCell inertPath) betaDom) rightAcc
          = composePath whiskerCell
              (composePath (composePath inertPath betaDom) rightAcc) := by
        rw [composePath_assoc whiskerCell inertPath betaDom,
          composePath_assoc whiskerCell (composePath inertPath betaDom) rightAcc]
      have reassocMovingCod : composePath
            (composePath (composePath whiskerCell inertPath) betaCod) rightAcc
          = composePath whiskerCell
              (composePath (composePath inertPath betaCod) rightAcc) := by
        rw [composePath_assoc whiskerCell inertPath betaCod,
          composePath_assoc whiskerCell (composePath inertPath betaCod) rightAcc]
      have reassocAccHigh : composePath (composePath leftAcc bodyCod)
            (composePath whiskerCell inertPath)
          = composePath (composePath leftAcc (composePath bodyCod whiskerCell))
              inertPath := by
        rw [← composePath_assoc (composePath leftAcc bodyCod) whiskerCell inertPath,
          composePath_assoc leftAcc bodyCod whiskerCell]
      have reassocAccLow : composePath (composePath leftAcc bodyDom)
            (composePath whiskerCell inertPath)
          = composePath (composePath leftAcc (composePath bodyDom whiskerCell))
              inertPath := by
        rw [← composePath_assoc (composePath leftAcc bodyDom) whiskerCell inertPath,
          composePath_assoc leftAcc bodyDom whiskerCell]
      rw [reassocMovingDom, reassocMovingCod, reassocAccHigh, reassocAccLow] at inner
      exact inner

/-- ★ **The Godement step is atomic**: under the shared `cellAlpha` prefix, the block-level
transpose-and-shift IS the block move at `inertPath := identityPath` (the two identity-path
laws bridge the inert-zone spellings). -/
theorem SpineGodementStep.toAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    AtomicTraceEquiv signature firstList secondList := by
  cases step with
  | @godement sourceMode middleMode targetMode oneCellFLow oneCellFMid oneCellFHigh
      oneCellGLow oneCellGMid oneCellGHigh cellAlpha cellAlphaUpper cellBeta cellBetaUpper
      leftAcc rightAcc rest =>
      have inner := AtomicTraceEquiv.blockMovePastCell cellBeta rightAcc cellAlphaUpper
        leftAcc (identityPath middleMode)
        (cellBetaUpper.spineDiff (composePath leftAcc oneCellFHigh) rightAcc rest)
      rw [composePath_identityPath_left oneCellGLow,
        composePath_identityPath_left oneCellGMid,
        composePath_identityPath_right (composePath leftAcc oneCellFHigh),
        composePath_identityPath_right (composePath leftAcc oneCellFMid)] at inner
      exact AtomicTraceEquiv.prependSpineDiff leftAcc (composePath oneCellGLow rightAcc)
        cellAlpha inner

/-- The block-level trace equivalence maps into the atomic closure — each Godement step by
`toAtomicTraceEquiv`, the closure operators one-to-one. -/
theorem SpineTraceEquiv.toAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : SpineTraceEquiv signature firstList secondList) :
    AtomicTraceEquiv signature firstList secondList := by
  induction traceEquiv with
  | ofStep step => exact step.toAtomicTraceEquiv
  | refl spineList => exact AtomicTraceEquiv.refl spineList
  | symm _ innerHypothesis => exact AtomicTraceEquiv.symm innerHypothesis
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis => exact AtomicTraceEquiv.consCongr atom innerHypothesis

/-- ★ **FREE-5**: the two closures COINCIDE — the block-level trace equivalence is exactly
the atomic swap closure, so the trace decision may work at atom granularity. -/
theorem spineTraceEquiv_iff_atomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
    SpineTraceEquiv signature firstList secondList
      ↔ AtomicTraceEquiv signature firstList secondList :=
  ⟨fun traceEquiv => traceEquiv.toAtomicTraceEquiv,
    fun atomicEquiv => atomicEquiv.toSpineTraceEquiv⟩

end FX1Poly.Polygraph
