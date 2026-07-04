import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainReadbackConv

/-! # ChainSplit — chain uniqueness + the split inverse to the chain builder

The reconstruction's surgery steps (the Godement step lifted onto chains, the trace-equivalence
induction) consume a chain over a spine-shaped list and need the chain over its REST suffix.
This file ships that decomposition kit:

  * `FramedSpineChain.tailChain` — the TOTAL tail extractor (the return type matches on the
    atom list, so there is no indexed-inversion case split — `nil` returns the unit);
  * ★ `FramedSpineChain.subsingletonEq` — **chain uniqueness**: two chains over the same atom
    list at the same anchored boundary are EQUAL — the inter-atom gluing is forced by the
    indices, so a chain is property-like data;
  * `RawTwoCellExpr.spineChainSplit` — the split INVERSE to `spineChainDiff`: from a chain
    over `cell.spineDiff leftAcc rightAcc restAtoms` anchored at the cell's domain frame,
    extract the chain over `restAtoms` anchored at its codomain frame (mirroring the builder's
    five arms, seams reversed);
  * ★ `FramedSpineChain.split_readback_convFull` — the split readback conversion: ANY chain
    over a spine-shaped list reads back convertible to the accumulator-whiskered cell composed
    with its split's readback.  By uniqueness the chain IS the builder applied to its own
    split, so the generalized readback conversion applies verbatim.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The total tail extractor -/

/-- The TOTAL tail extractor: on a chain over a cons list, the rest chain from the head atom's
codomain frame; on the empty chain, the unit.  The match lives in the RETURN TYPE, so no
indexed-inversion case split is ever needed at cons-shaped call sites — the type computes. -/
def FramedSpineChain.tailChain {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    {atoms : List (SpineAtom signature overallSource overallTarget)} →
    FramedSpineChain signature sourcePath targetPath atoms →
    (match atoms with
     | [] => PUnit
     | headAtom :: restAtoms =>
         FramedSpineChain signature
           (composePath headAtom.leftContext
             (composePath headAtom.generatorCod headAtom.rightContext))
           targetPath restAtoms)
  | _, _, _, .nil _ => PUnit.unit
  | _, _, _, .cons _ rest => rest

/-! ## Chain uniqueness -/

/-- The cons-eta view: a chain over a cons list IS the cons of its head atom onto its tail
(heterogeneously — the source path is a FREE variable here, so dependent elimination solves
the indices; at pinned-frame use sites the two types coincide and `eq_of_heq` lands the
homogeneous equation). -/
theorem FramedSpineChain.consEtaHeq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    {headAtom : SpineAtom signature overallSource overallTarget}
    {restAtoms : List (SpineAtom signature overallSource overallTarget)}
    (chain : FramedSpineChain signature sourcePath targetPath (headAtom :: restAtoms)) :
    HEq chain (FramedSpineChain.cons headAtom chain.tailChain) := by
  cases chain with
  | cons _ _ => exact HEq.refl _

/-- ★ **Chain uniqueness** — two chains over the same atom list at the same anchored boundary
are EQUAL: the head atom and every inter-atom boundary are forced by the indices, so a
`FramedSpineChain` is property-like data (the certificate that the list glues). -/
theorem FramedSpineChain.subsingletonEq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget} →
    {atoms : List (SpineAtom signature overallSource overallTarget)} →
    (firstChain secondChain : FramedSpineChain signature sourcePath targetPath atoms) →
    firstChain = secondChain
  | _, _, _, .nil _, secondChain => by
      cases secondChain with
      | nil => rfl
  | _, _, _, .cons atom firstRest, secondChain => by
      have secondEta : secondChain = FramedSpineChain.cons atom secondChain.tailChain :=
        eq_of_heq (FramedSpineChain.consEtaHeq secondChain)
      rw [secondEta]
      exact congrArg (fun restChain => FramedSpineChain.cons atom restChain)
        (FramedSpineChain.subsingletonEq firstRest secondChain.tailChain)

/-! ## The split inverse to the builder -/

/-- The **split** inverse to `spineChainDiff`: from a chain over
`cell.spineDiff leftAcc rightAcc restAtoms` anchored at the cell's DOMAIN frame, the chain over
`restAtoms` anchored at its CODOMAIN frame.  Mirrors the builder's five arms with the seams
reversed: `gen` takes the tail (the type computes at the cons), `id` is the chain itself,
`vcomp` peels the left factor then the right, the whisker arms re-anchor through the
`composePath` associativity seams. -/
def RawTwoCellExpr.spineChainSplit {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    {restTarget : ModalityPath signature.graph overallSource overallTarget} →
    {restAtoms : List (SpineAtom signature overallSource overallTarget)} →
    FramedSpineChain signature
      (composePath leftAccumulator (composePath localDom rightAccumulator))
      restTarget (cell.spineDiff leftAccumulator rightAccumulator restAtoms) →
    FramedSpineChain signature
      (composePath leftAccumulator (composePath localCod rightAccumulator))
      restTarget restAtoms
  | _, _, _, _, _, _, .gen _, _, _, chain => chain.tailChain
  | _, _, _, _, _, _, .id _, _, _, chain => chain
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, _, _, chain =>
      cellBeta.spineChainSplit leftAccumulator rightAccumulator
        (cellAlpha.spineChainSplit leftAccumulator rightAccumulator chain)
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, _, _, chain =>
      FramedSpineChain.castSource
        (reassocLeftWhisker leftAccumulator oneCell _ rightAccumulator)
        (body.spineChainSplit (composePath leftAccumulator oneCell) rightAccumulator
          (chain.castSource
            (reassocLeftWhisker leftAccumulator oneCell _ rightAccumulator).symm))
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, _, _, chain =>
      FramedSpineChain.castSource
        (reassocRightWhisker leftAccumulator _ oneCell rightAccumulator)
        (body.spineChainSplit leftAccumulator (composePath oneCell rightAccumulator)
          (chain.castSource
            (reassocRightWhisker leftAccumulator _ oneCell rightAccumulator).symm))

/-! ## The split readback conversion -/

/-- ★ **The split readback conversion**: ANY chain over a spine-shaped list reads back
convertible to the accumulator-whiskered cell vertically composed with its split's readback.
By chain uniqueness the chain IS the builder applied to its own split, so the generalized
readback conversion applies verbatim. -/
theorem FramedSpineChain.split_readback_convFull {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (leftAccumulator : ModalityPath signature.graph overallSource localSource)
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    {restTarget : ModalityPath signature.graph overallSource overallTarget}
    {restAtoms : List (SpineAtom signature overallSource overallTarget)}
    (chain : FramedSpineChain signature
      (composePath leftAccumulator (composePath localDom rightAccumulator))
      restTarget (cell.spineDiff leftAccumulator rightAccumulator restAtoms)) :
    TwoCellConvFull signature chain.readback
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft leftAccumulator
          (RawTwoCellExpr.whiskerRight rightAccumulator cell))
        (cell.spineChainSplit leftAccumulator rightAccumulator chain).readback) := by
  have readbackEq : chain.readback
      = (cell.spineChainDiff leftAccumulator rightAccumulator
          (cell.spineChainSplit leftAccumulator rightAccumulator chain)).readback :=
    congrArg FramedSpineChain.readback
      (FramedSpineChain.subsingletonEq chain
        (cell.spineChainDiff leftAccumulator rightAccumulator
          (cell.spineChainSplit leftAccumulator rightAccumulator chain)))
  rw [readbackEq]
  exact RawTwoCellExpr.spineChainDiff_readback_convFull leftAccumulator rightAccumulator cell
    (cell.spineChainSplit leftAccumulator rightAccumulator chain)

/-! ## Honesty marker -/

/-- **Honesty marker — the chain decomposition kit is SHIPPED.**  Chains are property-like
(`subsingletonEq`), every spine-shaped chain splits into its rest suffix (`spineChainSplit`,
the total inverse to the builder), and the split's readback converts against the whiskered
cell (`split_readback_convFull`).  This is the surgery substrate the Godement chain step and
the trace-equivalence reconstruction consume.  `= true`. -/
def fxMode_hasSpineChainSplit : Bool := true

end FX1Poly.Polygraph
