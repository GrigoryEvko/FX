import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellWordProblem
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjointStrings
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeNormalize

/-! # mode-3 floor — the readback past the `spine` quotient (the YES-direction, sharpened)

`AdjunctionTwoCellWordProblem` reduced the seed's full `TwoCellConv` decision to TWO obligations — a list-level
`traceDecision` (`Decidable (SpineTraceEquiv …)`) and a `reconstruct`
(`SpineTraceEquiv a.spine b.spine → TwoCellConv a b`, the readback past the `spine` quotient) — with the whole
NO-direction already discharged by the shipped soundness `TwoCellConv.spineTraceEquiv`.  This file attacks
`reconstruct`: it SHIPS the cell↔normal-form bridge, the Godement-step-as-`interchange` content (the genuine
mathematical core of the YES-direction), and a machine-checked REDUCTION of `reconstruct` to its
interchange-free-NORMAL-FORM restriction — leaving a strictly smaller, precisely-named residual.

## What this file ships (each piece zero-axiom)

  ★ `atomFrame` / `atomFrameSource` / `atomFrameTarget` — the **per-atom readback**: a `SpineAtom` (a generating
    2-cell with a left/right whiskering context) read back as the whiskered generator
    `whiskerLeft leftContext (whiskerRight rightContext (gen generator))`, the right-associated chain's link.
  ★ `convToInterchangeFreeNormalForm` — every cell is `TwoCellConv` to its interchange-free normal form `nf`
    (the normalizer `reduces`-to-normal-form chain is a reflexive-transitive interchange-free reduction, every
    step of which is a `TwoCellStep`, hence a `TwoCellConv`).  This is the cell→normal-form half of the bridge.
  ★ `interchangeFreeNormalForm_spine_eq` — `nf` PRESERVES the spine (`(nf cell).spine = cell.spine`): the spine
    is invariant under every interchange-free structural law (`TwoCellStepInterchangeFree.spine_eq`), and `nf` is
    reached by exactly those.  So normalizing does not move the trace class.
  ★ `framedGodementInterchangeConv` — a single Godement / `interchange` step lifted through whisker congruence to
    a `TwoCellConv` on the framed redex/reduct: the cell-level realization of ONE `SpineGodementStep`.  This is
    the "single-step lemma" the YES-direction is built from.
  ★ `godementWithTailConv` — the SAME, vertically composed with an arbitrary tail cell (via `vcompCongrLeft`):
    the reusable lift ingredient — a Godement transposition occurring at the HEAD of a right-associated chain is
    one `TwoCellConv` on the whole chain, leaving the tail untouched.
  ★ `adjunctionReconstructionFromNf` (★) — the **reduction**: the full `reconstruct`
    (`AdjunctionSpineTraceReconstruction`) follows from its interchange-free-normal-form restriction
    (`AdjunctionNfTraceReconstruction`).  Discharges the general-cell↔normal-form bridge:
    `cellFirst ≈ nf cellFirst`, `nf cellSecond ≈ cellSecond`, and the spine-preservation transports the trace
    equivalence onto the normal forms.  So the `reconstruct` half is now owed ONLY for two interchange-free
    normal forms (which ARE right-associated whiskered-atom chains), not for arbitrary cells.
  ★ `adjunctionTwoCellWordProblemModuloTraceAndNfReconstruction` — packages the seed's full
    `DecidableTwoCellConvFor` decision modulo `(traceDecision, nfReconstruct)`: supplying the list-level trace
    decision PLUS the normal-form-restricted readback inhabits the interface.  The `reconstruct` hypothesis of
    `adjunctionTwoCellWordProblemModuloTraceRoute` is thereby sharpened to its normal-form restriction.

## What is DEFERRED (the precise remaining gap toward the keystone) — gates stay `false`

The residual is `AdjunctionNfTraceReconstruction`: a list-level `SpineTraceEquiv` between two normal forms'
spines realized as a cell-level `TwoCellConv`.  Its honest obstruction is the BOUNDARY-INDEXED TOTAL READBACK a
direct induction on `SpineTraceEquiv` would require.  A `readbackNormalForm sourcePath targetPath : List SpineAtom
→ RawTwoCellExpr … sourcePath targetPath` CANNOT be a structural total function: the EMPTY list is the spine of
every IDENTITY 2-cell, whose boundary is REFLEXIVE (`sourcePath = targetPath`), so the only cell the empty case
can return is `RawTwoCellExpr.id` — which forces `sourcePath = targetPath` and so does NOT inhabit
`cell sourcePath targetPath` for an independent `targetPath` (and where the parallel hom is uninhabited there is
nothing to return at all).  Anchoring the FIRST atom at `sourcePath` fails for the dual reason — `atomFrame`'s
boundary is RIGID (`leftContext ∘ generatorDom ∘ rightContext`), with no whisker freedom to meet an arbitrary
`sourcePath`.  A `dite`-coherence chain (gluing each `atomFrame` to the running boundary by a decidable
path-equality check) is total only into a COMPUTED boundary, which the Godement step SHIFTS by the path-category
laws (associativity / right-identity) — so the two readbacks land at definitionally-distinct (only
propositionally-equal) boundaries and `TwoCellConv` between them does not even typecheck without a
heterogeneous, cast-threaded conversion; and the `dite`'s dependent motive does not reduce on the `else` branch.
Realizing `SpineTraceEquiv`'s `trans` needs a deterministic readback FUNCTION on the (non-spine) intermediate
difference-lists; realizing its `godement` needs every such list decomposed into the `vcomp (frame …) tail`
shape `godementWithTailConv` consumes.  That decomposition — a coherence-refined chain datatype carrying the
inter-atom boundary equalities, with `SpineTraceEquiv` lifted onto it — is the genuine remaining development.
Hence `fxMode_hasSpineTraceReconstruction` (the marker in `FreeTwoCellSpineGodement`) and
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false`; what this file adds is
the cell↔normal-form bridge + the single-step content + the machine-checked reduction of `reconstruct` to its
normal-form restriction.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the bridge is induction on a `ReflTransClosure` `Prop`; the Godement content is whisker / vcomp congruence over
`TwoCellStep.interchange`; the reduction is `rw` on the two spine-preservation equalities then `TwoCellConv.trans`).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The per-atom readback: a whiskered generator -/

/-- The **per-atom readback**: a spine atom (a generating 2-cell sandwiched between a left and right whiskering
context) read back as the whiskered generator `leftContext ◁ (rightContext ▷ gen generator)` — one link of the
right-associated chain a readback assembles.  Its boundary is the atom's stored `(leftContext ∘ generatorDom ∘
rightContext) ⇒ (leftContext ∘ generatorCod ∘ rightContext)`. -/
def atomFrame {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    RawTwoCellExpr signature
      (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext))
      (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) :=
  RawTwoCellExpr.whiskerLeft atom.leftContext
    (RawTwoCellExpr.whiskerRight atom.rightContext (RawTwoCellExpr.gen atom.generator))

/-- The source 1-cell of an atom's readback frame. -/
def atomFrameSource {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : ModalityPath signature.graph sourceMode targetMode :=
  composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)

/-- The target 1-cell of an atom's readback frame. -/
def atomFrameTarget {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : ModalityPath signature.graph sourceMode targetMode :=
  composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)

/-- Smoke: the readback frame of an atom lives at the boundary named by `atomFrameSource` / `atomFrameTarget`
(definitional) — the per-atom readback is well-anchored at the atom's stored contexts. -/
theorem atomFrame_boundary {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) :
    atomFrame atom = RawTwoCellExpr.whiskerLeft atom.leftContext
      (RawTwoCellExpr.whiskerRight atom.rightContext (RawTwoCellExpr.gen atom.generator)) := rfl

/-! ## The cell↔normal-form bridge -/

/-- The interchange-free normal form of a free 2-cell (the `Acc.rec` normalizer of the strongly-normalizing
interchange-free fragment). -/
def nfCell {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    RawTwoCellExpr signature sourcePath targetPath :=
  (interchangeFreeNormalizer signature sourcePath targetPath).normalize cell

/-- A reflexive-transitive chain of interchange-free rewrites is a `TwoCellConv` (each step is a `TwoCellStep`,
the closure threads through `TwoCellConv`'s reflexivity / transitivity). -/
theorem twoCellConv_ofInterchangeFreeReduction {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (chain : Core.ReflTransClosure
      (fun firstCell secondCell => TwoCellStepInterchangeFree signature firstCell secondCell)
      cellFirst cellSecond) :
    TwoCellConv signature cellFirst cellSecond :=
  interchangeFreeConv_imp_twoCellConv (Core.EquationalTheory.ofReduction chain)

/-- ★ **Every cell converts to its interchange-free normal form.**  The normalizer reduces `cell` to `nf cell`
by a reflexive-transitive interchange-free reduction, which is a `TwoCellConv`. -/
theorem convToInterchangeFreeNormalForm {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    TwoCellConv signature cell (nfCell cell) :=
  twoCellConv_ofInterchangeFreeReduction
    ((interchangeFreeNormalizer signature sourcePath targetPath).reducesToNormalForm cell)

/-- The spine is invariant under a reflexive-transitive interchange-free reduction (each step preserves it by
`TwoCellStepInterchangeFree.spine_eq`). -/
theorem spine_eq_ofInterchangeFreeReduction {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (chain : Core.ReflTransClosure
      (fun firstCell secondCell => TwoCellStepInterchangeFree signature firstCell secondCell)
      cellFirst cellSecond) :
    cellFirst.spine = cellSecond.spine := by
  induction chain with
  | refl _ => rfl
  | head firstStep _ inductionHypothesis => exact Eq.trans firstStep.spine_eq inductionHypothesis

/-- ★ **The interchange-free normal form has the SAME spine as the cell.**  Normalizing moves a cell only by
interchange-free structural laws, each spine-invariant — so the trace class is unchanged. -/
theorem interchangeFreeNormalForm_spine_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (nfCell cell).spine = cell.spine :=
  (spine_eq_ofInterchangeFreeReduction
    ((interchangeFreeNormalizer signature sourcePath targetPath).reducesToNormalForm cell)).symm

/-! ## The Godement-step-as-`interchange` content (the YES-direction core) -/

/-- ★ **A single Godement step, realized as a cell-level `TwoCellConv`.**  The `interchange` 3-cell
`(α ⊟ α') ⊠ (β ⊟ β') ⟶ (α ⊠ β) ⊟ (α' ⊠ β')`, lifted through left/right whisker congruence by an arbitrary
boundary context — the cell-level image of ONE `SpineGodementStep` on the framed redex/reduct. -/
theorem framedGodementInterchangeConv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh) :
    TwoCellConv signature
      (RawTwoCellExpr.whiskerLeft leftAcc (RawTwoCellExpr.whiskerRight rightAcc
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
          (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))))
      (RawTwoCellExpr.whiskerLeft leftAcc (RawTwoCellExpr.whiskerRight rightAcc
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
          (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)))) :=
  TwoCellConv.whiskerLeftCongr leftAcc
    (TwoCellConv.whiskerRightCongr rightAcc
      (TwoCellConv.ofStep
        (TwoCellStep.interchange cellAlpha cellAlphaUpper cellBeta cellBetaUpper)))

/-- ★ **The Godement transposition at the HEAD of a right-associated chain.**  The framed redex / reduct
vertically composed with an arbitrary tail cell — one `TwoCellConv` (via `vcompCongrLeft` over
`framedGodementInterchangeConv`) leaving the tail untouched.  This is the reusable lift ingredient: a
`SpineGodementStep` occurring at the head of a readback chain realizes as a single cell-level conversion. -/
theorem godementWithTailConv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    {tailTarget : ModalityPath signature.graph overallSource overallTarget}
    (tailCell : RawTwoCellExpr signature
      (composePath leftAcc (composePath (composePath fHigh gHigh) rightAcc)) tailTarget) :
    TwoCellConv signature
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft leftAcc (RawTwoCellExpr.whiskerRight rightAcc
          (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
            (RawTwoCellExpr.vcomp cellBeta cellBetaUpper)))) tailCell)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft leftAcc (RawTwoCellExpr.whiskerRight rightAcc
          (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
            (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)))) tailCell) :=
  TwoCellConv.vcompCongrLeft tailCell
    (framedGodementInterchangeConv leftAcc rightAcc cellAlpha cellAlphaUpper cellBeta cellBetaUpper)

/-! ## The reduction: `reconstruct` ⟸ its normal-form restriction -/

/-- The **normal-form-restricted readback obligation**: a list-level trace equivalence between two cells'
interchange-free NORMAL forms (which ARE right-associated whiskered-atom chains) realized as a cell-level
`TwoCellConv` of those normal forms.  Strictly smaller than the full `reconstruct`
(`AdjunctionSpineTraceReconstruction`): the general-cell↔normal-form bridge is already discharged below. -/
abbrev AdjunctionNfTraceReconstruction : Prop :=
  {sourceMode targetMode : adjunctionModeSignature.graph.Mode} →
  {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode} →
  (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
  SpineTraceEquiv adjunctionModeSignature (nfCell cellFirst).spine (nfCell cellSecond).spine →
  TwoCellConv adjunctionModeSignature (nfCell cellFirst) (nfCell cellSecond)

/-- ★ **The reduction.**  The full `reconstruct` follows from its normal-form restriction.  Given trace-equivalent
spines of `cellFirst`, `cellSecond`: the spines of their normal forms agree with theirs
(`interchangeFreeNormalForm_spine_eq`), so the trace equivalence transports onto the normal forms; the
normal-form readback then converts `nf cellFirst ≈ nf cellSecond`; and the cell↔normal-form bridge
(`convToInterchangeFreeNormalForm`, both sides) closes `cellFirst ≈ nf cellFirst ≈ nf cellSecond ≈ cellSecond`.
So the `reconstruct` half of the keystone residual is sharpened to `AdjunctionNfTraceReconstruction`. -/
theorem adjunctionReconstructionFromNf
    (nfReconstruct : AdjunctionNfTraceReconstruction) :
    AdjunctionSpineTraceReconstruction := by
  intro sourceMode targetMode sourcePath targetPath cellFirst cellSecond tracesEquiv
  have spineFirst : (nfCell cellFirst).spine = cellFirst.spine :=
    interchangeFreeNormalForm_spine_eq cellFirst
  have spineSecond : (nfCell cellSecond).spine = cellSecond.spine :=
    interchangeFreeNormalForm_spine_eq cellSecond
  have tracesEquivNf : SpineTraceEquiv adjunctionModeSignature
      (nfCell cellFirst).spine (nfCell cellSecond).spine := by
    rw [spineFirst, spineSecond]; exact tracesEquiv
  exact TwoCellConv.trans (convToInterchangeFreeNormalForm cellFirst)
    (TwoCellConv.trans (nfReconstruct cellFirst cellSecond tracesEquivNf)
      (TwoCellConv.symm (convToInterchangeFreeNormalForm cellSecond)))

/-- ★ **The seed's full 2-cell decision, modulo `(traceDecision, nfReconstruct)`.**  Packages
`adjunctionTwoCellWordProblemModuloTraceRoute` with the `reconstruct` hypothesis sharpened to its normal-form
restriction (via `adjunctionReconstructionFromNf`): supplying the list-level `traceDecision` PLUS the
normal-form-restricted readback inhabits the full `DecidableTwoCellConvFor adjunctionModeSignature`.  The whole
NO-direction is (still) free from soundness; the YES-direction is owed only for interchange-free normal forms. -/
def adjunctionTwoCellWordProblemModuloTraceAndNfReconstruction
    (traceDecision : AdjunctionSpineTraceDecision)
    (nfReconstruct : AdjunctionNfTraceReconstruction) :
    DecidableTwoCellConvFor adjunctionModeSignature :=
  adjunctionTwoCellWordProblemModuloTraceRoute traceDecision
    (adjunctionReconstructionFromNf nfReconstruct)

/-! ## Honesty marker -/

/-- **Honesty marker.**  `reconstruct` is NOT fully discharged: this file ships the cell↔normal-form bridge
(`convToInterchangeFreeNormalForm` + `interchangeFreeNormalForm_spine_eq`), the Godement-step-as-`interchange`
content (`framedGodementInterchangeConv` / `godementWithTailConv`), and the machine-checked REDUCTION of
`reconstruct` to its normal-form restriction (`adjunctionReconstructionFromNf`).  The residual
`AdjunctionNfTraceReconstruction` — realizing a `SpineTraceEquiv` of two NORMAL forms' spines as a cell-level
`TwoCellConv` — remains: it needs a boundary-indexed total readback of the (non-spine, difference-list)
intermediate lists, blocked by the genuine totality / path-category-cast obstruction documented in the module
header.  Hence `fxMode_hasSpineTraceReconstruction` / `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasDecidableTwoCellEquality` stay `false`.  `= false`. -/
def fxMode_hasNormalFormSpineReadback : Bool := false

end FX1Poly.Tier0
