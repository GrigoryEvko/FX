import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainSplit

/-! # ChainReadbackCongruence — readback congruence over a shared spineDiff prefix

The Godement chain lift peels the step's redex/reduct lists layer by layer: both lists are
`spineDiff`s of the SAME leading cell over two different inner lists.  This file ships the
peeling engine:

  * `FramedSpineChain.headSourceEq` — the total head-frame extractor: on a cons list the
    chain's source IS the head atom's domain frame (the match lives in the return type);
  * ★ `RawTwoCellExpr.spineDiff_readback_congruence` — chains over `cell.spineDiff` of the
    same cell over two different rest-lists have convertible readbacks whenever the two rest
    chains do, AT EVERY ANCHOR.  The universal anchor in the hypothesis is what makes the
    recursion survive degenerate sub-cells (an identity sub-cell passes the outer, unpinned
    anchor straight through to the hypothesis; a generator pins it to the atom's codomain
    frame).  No source-pinning, no casts — the whisker arms are direct recursion at the
    extended accumulators.

What remains for the Godement lift is the swap CORE (the two transposed middle blocks at an
arbitrary anchor — the Mazurkiewicz commutation); this congruence reduces the full step to
exactly that core.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The total head-frame extractor -/

/-- The TOTAL head-frame extractor: on a chain over a cons list, the source path IS the head
atom's domain frame; on the empty chain, source equals target.  The match lives in the RETURN
TYPE, so no indexed-inversion case split is needed. -/
theorem FramedSpineChain.headSourceEq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    {atoms : List (SpineAtom signature overallSource overallTarget)} →
    FramedSpineChain signature sourcePath targetPath atoms →
    (match atoms with
     | [] => sourcePath = targetPath
     | headAtom :: _ =>
         sourcePath = composePath headAtom.leftContext
           (composePath headAtom.generatorDom headAtom.rightContext))
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ _ => rfl

/-! ## The readback congruence over a shared spineDiff prefix -/

/-- ★ **Readback congruence over a shared `spineDiff` prefix**: chains over
`cell.spineDiff leftAcc rightAcc restAtomsOne` and `cell.spineDiff leftAcc rightAcc
restAtomsTwo` — the SAME cell over two different rest-lists — have convertible readbacks
whenever the two rest chains do at EVERY anchor.  The universal anchor is essential: the `id`
arm passes the outer (unpinned) anchor straight through, the `gen` arm pins it to the atom's
codomain frame, `vcomp` stacks the hypothesis through the second factor, and the whisker arms
recurse at the extended accumulators with no casts (the atom lists are literally shared). -/
theorem RawTwoCellExpr.spineDiff_readback_congruence {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    {restTarget : ModalityPath signature.graph overallSource overallTarget} →
    {restAtomsOne restAtomsTwo : List (SpineAtom signature overallSource overallTarget)} →
    (restCongr : ∀ {anchorPath : ModalityPath signature.graph overallSource overallTarget}
        (restChainOne : FramedSpineChain signature anchorPath restTarget restAtomsOne)
        (restChainTwo : FramedSpineChain signature anchorPath restTarget restAtomsTwo),
        TwoCellConvFull signature restChainOne.readback restChainTwo.readback) →
    ∀ {sourcePath : ModalityPath signature.graph overallSource overallTarget}
      (chainOne : FramedSpineChain signature sourcePath restTarget
        (cell.spineDiff leftAccumulator rightAccumulator restAtomsOne))
      (chainTwo : FramedSpineChain signature sourcePath restTarget
        (cell.spineDiff leftAccumulator rightAccumulator restAtomsTwo)),
      TwoCellConvFull signature chainOne.readback chainTwo.readback
  | _, _, leftAccumulator, rightAccumulator, _, _, .gen generator => by
      intro restCongr sourcePath chainOne chainTwo
      have sourceEq := FramedSpineChain.headSourceEq chainOne
      subst sourceEq
      have etaOne : chainOne = FramedSpineChain.cons
          ⟨_, _, leftAccumulator, _, _, generator, rightAccumulator⟩ chainOne.tailChain :=
        eq_of_heq (FramedSpineChain.consEtaHeq chainOne)
      have etaTwo : chainTwo = FramedSpineChain.cons
          ⟨_, _, leftAccumulator, _, _, generator, rightAccumulator⟩ chainTwo.tailChain :=
        eq_of_heq (FramedSpineChain.consEtaHeq chainTwo)
      rw [etaOne, etaTwo]
      exact TwoCellConvFull.vcompCongrRight _
        (restCongr chainOne.tailChain chainTwo.tailChain)
  | _, _, _, _, _, _, .id _ => by
      intro restCongr sourcePath chainOne chainTwo
      exact restCongr chainOne chainTwo
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta => by
      intro restCongr sourcePath chainOne chainTwo
      exact RawTwoCellExpr.spineDiff_readback_congruence leftAccumulator rightAccumulator
        cellAlpha
        (fun {anchorPath} innerChainOne innerChainTwo =>
          RawTwoCellExpr.spineDiff_readback_congruence leftAccumulator rightAccumulator
            cellBeta restCongr innerChainOne innerChainTwo)
        chainOne chainTwo
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body => by
      intro restCongr sourcePath chainOne chainTwo
      exact RawTwoCellExpr.spineDiff_readback_congruence
        (composePath leftAccumulator oneCell) rightAccumulator body restCongr
        chainOne chainTwo
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body => by
      intro restCongr sourcePath chainOne chainTwo
      exact RawTwoCellExpr.spineDiff_readback_congruence
        leftAccumulator (composePath oneCell rightAccumulator) body restCongr
        chainOne chainTwo

/-! ## Honesty marker -/

/-- **Honesty marker — the spineDiff peeling engine is SHIPPED.**  Readback conversion of
chain pairs propagates through a shared `spineDiff` prefix at every anchor
(`spineDiff_readback_congruence`).  STILL OPEN for the Godement chain lift: the swap CORE —
the two transposed middle blocks realized as a readback conversion at an arbitrary anchor
(the Mazurkiewicz commutation), to which this congruence reduces the full step.  `= true`. -/
def fxMode_hasSpineDiffReadbackCongruence : Bool := true

end FX1Poly.Polygraph
