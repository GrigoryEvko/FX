import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedTriangleReducer
import FX1Poly.Polygraph.Rewriting.Confluence.ConvergentNormalizerOfReducer

/-! # SaturatedFragmentNormalize — the saturated fragment's computable normalizer (SAT-NF brick C)

The three reducer bricks assemble into the generic normalizer: `saturatedReduceOnce` is
computable (B1/B2a), sound (B2a), and complete (B2b), and the fragment is strongly
normalizing (brick A), so `Core.ConvergentNormalizer.ofReducer` iterates it along the
`Acc` witness with `Acc.rec` — the well-founded recursion PRIMITIVE, axiom-free, NOT
`WellFounded.fix` — halting at the fragment normal form.  Same idiom as the free case's
`interchangeFreeNormalizer`.

  * ★ `saturatedFragmentNormalizer` — `normalize` / `reducesToNormalForm` /
    `normalFormIsNormal` for the interchange-free saturated fragment, NO confluence
    needed;
  * `saturatedFragmentNormalize_conv` — the normal form stays in the cell's SATURATED
    class (each fragment step is a `SaturatedTwoCellConv`, the reduction chain
    composes by transitivity).

HONESTY: this is the fragment NORMALIZER, not yet the fragment DECISION — normal-form
UNIQUENESS needs the fragment's local confluence (brick D: the triangle × structural
critical pairs; the interchange peak is withdrawn, so genuinely joinable) and Newman
over the shipped SN.  The saturated completeness (the FREE-trace delegation of the
residual NF equality) is SAT-COMPLETE's.  Markers stay until their content lands. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The saturated fragment's normalizer**: iterate the sound+complete reducer along
the fragment's strong normalization.  Parameterised by the boundary 1-cells, so the
carrier is the fixed-boundary 2-cell type the abstract engine expects. -/
def saturatedFragmentNormalizer
    {sourceMode targetMode : AdjunctionMode}
    (sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode) :
    Core.ConvergentNormalizer
      (fun (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) =>
        SaturatedStepInterchangeFree cellA cellB) :=
  Core.ConvergentNormalizer.ofReducer
    saturatedReduceOnce
    (fun fired => saturatedReduceOnce_sound fired)
    (fun halted next => saturatedReduceOnce_isNormal_of_none halted next)
    (fun cell => saturatedStepInterchangeFree_isStronglyNormalizing cell)

/-- The normal form stays in the cell's saturated class: every fragment step of the
reduction chain is a `SaturatedTwoCellConv` (`toSaturatedConv`), composed by
transitivity along the chain. -/
theorem saturatedFragmentNormalize_conv
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    SaturatedTwoCellConv cell
      ((saturatedFragmentNormalizer sourcePath targetPath).normalize cell) := by
  have chainToNormal :=
    (saturatedFragmentNormalizer sourcePath targetPath).reducesToNormalForm cell
  generalize (saturatedFragmentNormalizer sourcePath targetPath).normalize cell
    = normalForm at chainToNormal
  induction chainToNormal with
  | refl point => exact SaturatedTwoCellConv.refl point
  | head firstStep _restChain innerHypothesis =>
      exact SaturatedTwoCellConv.trans firstStep.toSaturatedConv innerHypothesis

end FX1Poly.Polygraph
