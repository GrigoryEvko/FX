import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine

/-! # mode-3 — the spine boundary-WORD-chain discipline (the label-boundary substrate, STRING-JOINT r2)

The length-only boundary chain `SpineBoundaryChained` (`SpineBoundaryChain.lean`) indexes an atom list by a
`Nat` boundary WIDTH and chains the widths through the spine (each atom fires at the running width, hands its
target width to the tail).  The STRING no-loops flip needs the WORD analog: the same chain over the actual
boundary 1-cell (a `ModalityPath`), so a head atom's boundary decomposes as
`leftContext · generatorDom · rightContext`.  That decomposition is exactly the `labelsEq` hypothesis the
shipped `stringCapWindow_notCupWord` (the FC-1 `capPin` projection) consumes, and (via `pathLabels`) its length
gives the window-in-range half.

This file ships that WORD-level substrate, mirroring the length version arm-for-arm — the length re-associations
(`ModalityPath.length_composePath` + `Nat.add_assoc`) become raw `composePath_assoc` rewrites over the free 1-cell
category (`Signature.lean`):

  * `SpineBoundaryWordChained` — the word-chain discipline on atom lists, indexed by a boundary `ModalityPath`,
    with cons inversion (`spineBoundaryWordChained_tail`);
  * `spineBoundaryWordChained_spineDiff` (production) — a cell's spine difference-list is word-chained from its
    SOURCE boundary word whenever the rest is word-chained from its TARGET boundary word;
  * `RawTwoCellExpr.spineBoundaryWordChained_spine` — the initial-state seed: every cell's spine is word-chained
    from its source 1-cell (the identity accumulators collapse via `composePath_identityPath_left/right`).

This is pure `composePath` bookkeeping, cons-only / structural — no mathematical content, no new list algebra
(the `composePath` category laws are already shipped in `Signature.lean`).  The consumer (WALL 2's reachable
`capPin` fold) reads the head decomposition off `headFires` at each cap atom.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The word-chain discipline -/

/-- The boundary-WORD-chain discipline on spine-atom lists: every atom fires exactly at the running boundary
WORD (its `leftContext · generatorDom · rightContext`) and hands its target boundary word
(`leftContext · generatorCod · rightContext`) to the tail.  The empty list is chained at any boundary word (it
constrains nothing).  This is the free-1-cell (`ModalityPath`) analog of the length-only `SpineBoundaryChained`. -/
inductive SpineBoundaryWordChained {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    ModalityPath signature.graph sourceMode targetMode →
    List (SpineAtom signature sourceMode targetMode) → Prop where
  /-- The empty spine is chained at any boundary word. -/
  | nil (boundaryWord : ModalityPath signature.graph sourceMode targetMode) :
      SpineBoundaryWordChained boundaryWord []
  /-- A cons is chained when the head fires at the running boundary word and the tail is chained at the head's
  target boundary word. -/
  | cons {boundaryWord : ModalityPath signature.graph sourceMode targetMode}
      (atom : SpineAtom signature sourceMode targetMode)
      {rest : List (SpineAtom signature sourceMode targetMode)}
      (headFires : boundaryWord
        = composePath atom.leftContext (composePath atom.generatorDom atom.rightContext))
      (tailChained : SpineBoundaryWordChained
        (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest) :
      SpineBoundaryWordChained boundaryWord (atom :: rest)

/-- Cons inversion for the word-chain discipline: the head fires at the running boundary word and the tail is
chained at the head's target boundary word. -/
theorem spineBoundaryWordChained_tail {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {boundaryWord : ModalityPath signature.graph sourceMode targetMode}
    {atom : SpineAtom signature sourceMode targetMode}
    {rest : List (SpineAtom signature sourceMode targetMode)}
    (chained : SpineBoundaryWordChained boundaryWord (atom :: rest)) :
    boundaryWord = composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)
      ∧ SpineBoundaryWordChained
          (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) rest := by
  cases chained with
  | cons _ headFires tailChained => exact ⟨headFires, tailChained⟩

/-! ## Production: a cell's spine difference-list is boundary-word-chained -/

/-- **Production.**  A cell's spine difference-list is word-chained from its SOURCE boundary word whenever the
rest is word-chained from its TARGET boundary word — each generator fires at the boundary word its whisker
accumulators and source 1-cell describe, and vertical composition threads the middle boundary word.  The whisker
arms re-associate the `composePath` accumulators via the shipped category associativity (`composePath_assoc`),
the word analog of the length version's `Nat.add_assoc` re-associations. -/
theorem spineBoundaryWordChained_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    SpineBoundaryWordChained (composePath leftAccumulator (composePath localCod rightAccumulator)) rest →
    SpineBoundaryWordChained (composePath leftAccumulator (composePath localDom rightAccumulator))
      (cell.spineDiff leftAccumulator rightAccumulator rest)
  | _, _, leftAccumulator, rightAccumulator, _, _, .gen generator, rest, restChained => by
      dsimp only [RawTwoCellExpr.spineDiff]
      exact SpineBoundaryWordChained.cons _ rfl restChained
  | _, _, _, _, _, _, .id _, _, restChained => restChained
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, rest, restChained =>
      spineBoundaryWordChained_spineDiff leftAccumulator rightAccumulator cellAlpha
        (cellBeta.spineDiff leftAccumulator rightAccumulator rest)
        (spineBoundaryWordChained_spineDiff leftAccumulator rightAccumulator cellBeta rest restChained)
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell bodySourcePath bodyTargetPath body, rest,
      restChained => by
      dsimp only [RawTwoCellExpr.spineDiff]
      have restChainedShifted : SpineBoundaryWordChained
          (composePath (composePath leftAccumulator oneCell)
            (composePath bodyTargetPath rightAccumulator)) rest := by
        rw [composePath_assoc leftAccumulator oneCell (composePath bodyTargetPath rightAccumulator),
          ← composePath_assoc oneCell bodyTargetPath rightAccumulator]
        exact restChained
      have producedShifted := spineBoundaryWordChained_spineDiff
        (composePath leftAccumulator oneCell) rightAccumulator body rest restChainedShifted
      rw [composePath_assoc oneCell bodySourcePath rightAccumulator,
        ← composePath_assoc leftAccumulator oneCell (composePath bodySourcePath rightAccumulator)]
      exact producedShifted
  | _, _, leftAccumulator, rightAccumulator, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ bodySourcePath bodyTargetPath oneCell body, rest,
      restChained => by
      dsimp only [RawTwoCellExpr.spineDiff]
      have restChainedShifted : SpineBoundaryWordChained
          (composePath leftAccumulator (composePath bodyTargetPath (composePath oneCell rightAccumulator)))
          rest := by
        rw [← composePath_assoc bodyTargetPath oneCell rightAccumulator]
        exact restChained
      have producedShifted := spineBoundaryWordChained_spineDiff
        leftAccumulator (composePath oneCell rightAccumulator) body rest restChainedShifted
      rw [composePath_assoc bodySourcePath oneCell rightAccumulator]
      exact producedShifted

/-! ## The initial-state seed -/

/-- Every cell's spine is word-chained from its source 1-cell — the boundary-word invariant holds at the
empty-accumulator flattening the no-loops fold starts from.  The identity accumulators collapse via the shipped
category unit laws (`composePath_identityPath_left` / `_right`). -/
theorem RawTwoCellExpr.spineBoundaryWordChained_spine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    SpineBoundaryWordChained sourcePath cell.spine := by
  have chainedPadded := spineBoundaryWordChained_spineDiff (identityPath sourceMode)
    (identityPath targetMode) cell [] (SpineBoundaryWordChained.nil _)
  have boundaryCollapses :
      composePath (identityPath (graph := signature.graph) sourceMode)
        (composePath sourcePath (identityPath (graph := signature.graph) targetMode)) = sourcePath := by
    rw [composePath_identityPath_right sourcePath]
    exact composePath_identityPath_left sourcePath
  rw [boundaryCollapses] at chainedPadded
  exact chainedPadded

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the spine boundary-WORD-chain substrate is SHIPPED.**  `SpineBoundaryWordChained` (the
`ModalityPath`-indexed chain discipline + cons inversion), the production `spineBoundaryWordChained_spineDiff`
(a cell's spine difference-list word-chained from its source boundary word, whisker arms via `composePath_assoc`),
and the initial-state seed `RawTwoCellExpr.spineBoundaryWordChained_spine`.  This is the word analog of the shipped
length-only `SpineBoundaryChained`; at each head atom it delivers the boundary decomposition
`boundaryWord = leftContext · generatorDom · rightContext` that the shipped `stringCapWindow_notCupWord`
(FC-1 `capPin` projection) consumes.  All UNCONDITIONAL, zero-axiom.  `= true`. -/
def fxMode_hasSpineBoundaryWordChainSubstrate : Bool := true

end FX1Poly.Polygraph
