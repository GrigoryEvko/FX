import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FramedSpineChain
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality

/-! # SpineChainBuilder — a boundary-coherent chain over every cell's spine (chain existence)

`FramedSpineChain` (FREE-1) made the readback TOTAL by carrying the inter-atom boundary
equalities in the chain's indices.  This file ships the EXISTENCE half of chain reconstruction:
every free 2-cell's spine IS chained — built by structural recursion on the cell, mirroring
`spineDiff`'s own difference-list architecture arm for arm.

  * `FramedSpineChain.castSource` / `castTarget` — chain transport along a boundary-path
    equality (explicit-motive `Eq.rec`; the atom index is untouched — only path indices move);
  * `castSource_readback` / `castTarget_readback` — transport commutes with the readback
    (the cast chain reads back as the `castBoundary` of the readback);
  * ★ `RawTwoCellExpr.spineChainDiff` — the difference-list builder: given a chain over the
    rest atoms anchored at the cell's codomain frame, a chain over `cell.spineDiff` anchored at
    its domain frame.  `gen` conses the atom spineDiff produces (indices on the nose); `id` and
    `vcomp` are the rest / threading (definitional); the two whisker arms re-anchor through
    `composePath` associativity via `castSource`, with casts on the argument and result chains,
    never inside the recursive calls;
  * ★ `RawTwoCellExpr.cellChain` — the spine-anchored corollary: a `FramedSpineChain` from
    `sourcePath` to `targetPath` over `cell.spine` (identity accumulators; the left identity
    seam is definitional, the right discharged by `composePath_identityPath_right` transport).

Consumed by the readback-Conv half of chain existence and by the realized-chain bridge.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Chain transport -/

/-- Transport a chain along an equality of its SOURCE boundary path (explicit-motive `Eq.rec`;
the atom index is untouched — only the path index moves). -/
def FramedSpineChain.castSource {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath sourcePath' targetPath : ModalityPath signature.graph overallSource overallTarget}
    {atoms : List (SpineAtom signature overallSource overallTarget)}
    (pathEq : sourcePath = sourcePath')
    (chain : FramedSpineChain signature sourcePath targetPath atoms) :
    FramedSpineChain signature sourcePath' targetPath atoms :=
  Eq.rec (motive := fun path _ => FramedSpineChain signature path targetPath atoms) chain pathEq

/-- Transport a chain along an equality of its TARGET boundary path. -/
def FramedSpineChain.castTarget {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath targetPath' : ModalityPath signature.graph overallSource overallTarget}
    {atoms : List (SpineAtom signature overallSource overallTarget)}
    (pathEq : targetPath = targetPath')
    (chain : FramedSpineChain signature sourcePath targetPath atoms) :
    FramedSpineChain signature sourcePath targetPath' atoms :=
  Eq.rec (motive := fun path _ => FramedSpineChain signature sourcePath path atoms) chain pathEq

/-- Source transport commutes with the readback: the cast chain reads back as the
`castBoundary` of the readback. -/
theorem FramedSpineChain.castSource_readback {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath sourcePath' targetPath : ModalityPath signature.graph overallSource overallTarget}
    {atoms : List (SpineAtom signature overallSource overallTarget)}
    (pathEq : sourcePath = sourcePath')
    (chain : FramedSpineChain signature sourcePath targetPath atoms) :
    (chain.castSource pathEq).readback
      = RawTwoCellExpr.castBoundary pathEq rfl chain.readback := by
  cases pathEq; rfl

/-- Target transport commutes with the readback. -/
theorem FramedSpineChain.castTarget_readback {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath targetPath' : ModalityPath signature.graph overallSource overallTarget}
    {atoms : List (SpineAtom signature overallSource overallTarget)}
    (pathEq : targetPath = targetPath')
    (chain : FramedSpineChain signature sourcePath targetPath atoms) :
    (chain.castTarget pathEq).readback
      = RawTwoCellExpr.castBoundary rfl pathEq chain.readback := by
  cases pathEq; rfl

/-! ## The whisker re-anchoring seams -/

/-- The LEFT-whisker re-anchoring seam: absorbing the whiskering 1-cell into the left
accumulator re-associates the frame path. -/
private theorem reassocLeftWhisker {signature : ModeSignature}
    {modeA modeB modeC modeD modeE : signature.graph.Mode}
    (leftAccumulator : ModalityPath signature.graph modeA modeB)
    (oneCell : ModalityPath signature.graph modeB modeC)
    (bodyPath : ModalityPath signature.graph modeC modeD)
    (rightAccumulator : ModalityPath signature.graph modeD modeE) :
    composePath (composePath leftAccumulator oneCell) (composePath bodyPath rightAccumulator)
      = composePath leftAccumulator
          (composePath (composePath oneCell bodyPath) rightAccumulator) :=
  (composePath_assoc leftAccumulator oneCell (composePath bodyPath rightAccumulator)).trans
    (congrArg (composePath leftAccumulator)
      (composePath_assoc oneCell bodyPath rightAccumulator).symm)

/-- The RIGHT-whisker re-anchoring seam: absorbing the whiskering 1-cell into the right
accumulator re-associates the frame path. -/
private theorem reassocRightWhisker {signature : ModeSignature}
    {modeA modeB modeC modeD modeE : signature.graph.Mode}
    (leftAccumulator : ModalityPath signature.graph modeA modeB)
    (bodyPath : ModalityPath signature.graph modeB modeC)
    (oneCell : ModalityPath signature.graph modeC modeD)
    (rightAccumulator : ModalityPath signature.graph modeD modeE) :
    composePath leftAccumulator (composePath bodyPath (composePath oneCell rightAccumulator))
      = composePath leftAccumulator
          (composePath (composePath bodyPath oneCell) rightAccumulator) :=
  congrArg (composePath leftAccumulator)
    (composePath_assoc bodyPath oneCell rightAccumulator).symm

/-! ## The difference-list chain builder -/

/-- ★ **The difference-list chain builder** — a `FramedSpineChain` over every cell's
`spineDiff`, mirroring its five arms: given a rest chain anchored at the cell's CODOMAIN frame
(`leftAcc ∘ localCod ∘ rightAcc`), produce a chain over `cell.spineDiff leftAcc rightAcc rest`
anchored at its DOMAIN frame.  `gen` conses exactly the atom `spineDiff` produces; `id` returns
the rest; `vcomp` threads the second factor's chain into the first; the whisker arms recurse at
the extended accumulator and re-anchor both the argument and the result through `composePath`
associativity (`castSource` — the casts never sit inside the recursive calls). -/
def RawTwoCellExpr.spineChainDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    {restTarget : ModalityPath signature.graph overallSource overallTarget} →
    {restAtoms : List (SpineAtom signature overallSource overallTarget)} →
    FramedSpineChain signature
      (composePath leftAccumulator (composePath localCod rightAccumulator))
      restTarget restAtoms →
    FramedSpineChain signature
      (composePath leftAccumulator (composePath localDom rightAccumulator))
      restTarget (cell.spineDiff leftAccumulator rightAccumulator restAtoms)
  | _, _, leftAccumulator, rightAccumulator, _, _, .gen generator, _, _, restChain =>
      FramedSpineChain.cons
        ⟨_, _, leftAccumulator, _, _, generator, rightAccumulator⟩ restChain
  | _, _, _, _, _, _, .id _, _, _, restChain => restChain
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, _, _, restChain =>
      cellAlpha.spineChainDiff leftAccumulator rightAccumulator
        (cellBeta.spineChainDiff leftAccumulator rightAccumulator restChain)
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, _, _, restChain =>
      FramedSpineChain.castSource
        (reassocLeftWhisker leftAccumulator oneCell _ rightAccumulator)
        (body.spineChainDiff (composePath leftAccumulator oneCell) rightAccumulator
          (restChain.castSource
            (reassocLeftWhisker leftAccumulator oneCell _ rightAccumulator).symm))
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, _, _, restChain =>
      FramedSpineChain.castSource
        (reassocRightWhisker leftAccumulator _ oneCell rightAccumulator)
        (body.spineChainDiff leftAccumulator (composePath oneCell rightAccumulator)
          (restChain.castSource
            (reassocRightWhisker leftAccumulator _ oneCell rightAccumulator).symm))

/-! ## The spine-anchored corollary -/

/-- ★ **Chain existence for every cell's spine**: a boundary-coherent chain from `sourcePath`
to `targetPath` over `cell.spine` — the builder at identity accumulators over the empty rest
chain, with the right identity-path seams discharged by transport (the left seams are
definitional). -/
def RawTwoCellExpr.cellChain {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    FramedSpineChain signature sourcePath targetPath cell.spine :=
  FramedSpineChain.castTarget (composePath_identityPath_right targetPath)
    (FramedSpineChain.castSource (composePath_identityPath_right sourcePath)
      (cell.spineChainDiff (identityPath sourceMode) (identityPath targetMode)
        (FramedSpineChain.nil (composePath targetPath (identityPath targetMode)))))

/-! ## Honesty marker -/

/-- **Honesty marker — chain EXISTENCE is SHIPPED (the constructive half of chain
reconstruction).**  Every free 2-cell's spine is chained: `spineChainDiff` builds a
`FramedSpineChain` over `cell.spineDiff` by structural recursion mirroring the difference-list
flattening, and `cellChain` anchors it at the cell's own boundary over `cell.spine`.  NOT yet
shipped: the readback Conv (the chain of a cell's spine reads back CONVERTIBLE to the cell —
the other half of chain existence), after which the Godement chain step and the generic trace
reconstruction assemble.  `= true`. -/
def fxMode_hasSpineChainBuilder : Bool := true

end FX1Poly.Polygraph
