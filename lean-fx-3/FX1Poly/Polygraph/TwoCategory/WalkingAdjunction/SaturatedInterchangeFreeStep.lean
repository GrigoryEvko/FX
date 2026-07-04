import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFree

/-! # SaturatedInterchangeFreeStep — the NF-bearing saturated fragment (triangles, interchange withdrawn)

The combined saturated rewrite `SaturatedTwoCellStep` is strongly normalizing but NOT locally
confluent — the Godement interchange peak does not join (`interchangeWitness_notLocallyConfluent`),
so no unique-normal-form route exists over the FULL rule set.  The honest normal-form architecture
is therefore TWO-LAYERED, mirroring the free case: rewrite with the triangles PLUS the eleven
structural laws while WITHDRAWING interchange (the only non-confluence source), and hand the
residual equality of the resulting normal forms — spine trace equivalence — to the FREE arc's
decided trace layer.  This file ships layer one's relation:

  * `SaturatedStepInterchangeFree` — the walking-adjunction fragment: every INTERCHANGE-FREE
    structural step (`ofStructural`), both bare triangles, both snake-prefix completions, and the
    full one-hole congruence closure (so a triangle redex fires in any sub-position);
  * `toSaturatedTwoCellStep` — the fragment embeds ctor-for-ctor into the combined rewrite
    (`ofStructural` through the interchange-free-to-full embedding);
  * `saturatedStepInterchangeFree_isStronglyNormalizing` — SN is FREE: accessibility descends to
    a subrelation, so the combined rewrite's unconditional termination carries over verbatim;
  * `toSaturatedConv` — every fragment step is a saturated convertibility (soundness for the
    normalizer this fragment will carry).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fragment relation -/

/-- ★ The **interchange-free saturated fragment** over the walking-adjunction signature: the
eleven structural laws (Godement `interchange` WITHDRAWN — the one non-confluence source), the
LEFT and RIGHT bare triangles, the LEFT and RIGHT snake-prefix completions, and the full one-hole
congruence closure.  The normal-form-bearing rewrite of the two-layer saturated decision: its
normal forms are triangle-free interchange-free chains whose residual equality is the FREE trace
class. -/
inductive SaturatedStepInterchangeFree :
    {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath → Prop where
  /-- Embed any INTERCHANGE-FREE structural step (the eleven laws). -/
  | ofStructural {sourceMode targetMode : AdjunctionMode}
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath} :
      TwoCellStepInterchangeFree adjunctionModeSignature cellA cellB →
      SaturatedStepInterchangeFree cellA cellB
  /-- The bare LEFT triangle `leftSnake ⤳ id_L`. -/
  | leftBareSnake :
      SaturatedStepInterchangeFree adjunctionSeedLeftSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.left))
  /-- The LEFT snake-prefix completion `(η▷L)⊟((L◁ε)⊟rest) ⤳ rest`. -/
  | leftSnakePrefix {targetPath : ModalityPath adjunctionGraph AdjunctionMode.base AdjunctionMode.tip}
      (rest : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.left) targetPath) :
      SaturatedStepInterchangeFree
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell)
            rest))
        rest
  /-- The bare RIGHT triangle `rightSnake ⤳ id_R`. -/
  | rightBareSnake :
      SaturatedStepInterchangeFree adjunctionSeedRightSnake
        (RawTwoCellExpr.id (signature := adjunctionModeSignature)
          (singletonModalityPath AdjunctionModality.right))
  /-- The RIGHT snake-prefix completion `(R◁η)⊟((ε▷R)⊟rest) ⤳ rest`. -/
  | rightSnakePrefix {targetPath : ModalityPath adjunctionGraph AdjunctionMode.tip AdjunctionMode.base}
      (rest : RawTwoCellExpr adjunctionModeSignature
        (singletonModalityPath AdjunctionModality.right) targetPath) :
      SaturatedStepInterchangeFree
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
            (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
              (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell)
            rest))
        rest
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
      (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH) :
      SaturatedStepInterchangeFree cellAlpha cellAlpha' →
      SaturatedStepInterchangeFree (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {sourceMode targetMode : AdjunctionMode}
      {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
      (cellAlpha : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG)
      {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} :
      SaturatedStepInterchangeFree cellBeta cellBeta' →
      SaturatedStepInterchangeFree (RawTwoCellExpr.vcomp cellAlpha cellBeta)
        (RawTwoCellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering. -/
  | whiskerLeftCongr {sourceMode middleMode targetMode : AdjunctionMode}
      (oneCell : ModalityPath adjunctionGraph sourceMode middleMode)
      {oneCellG oneCellH : ModalityPath adjunctionGraph middleMode targetMode}
      {cellBeta cellBeta' : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH} :
      SaturatedStepInterchangeFree cellBeta cellBeta' →
      SaturatedStepInterchangeFree (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {sourceMode middleMode targetMode : AdjunctionMode}
      {oneCellF oneCellG : ModalityPath adjunctionGraph sourceMode middleMode}
      (oneCell : ModalityPath adjunctionGraph middleMode targetMode)
      {cellAlpha cellAlpha' : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG} :
      SaturatedStepInterchangeFree cellAlpha cellAlpha' →
      SaturatedStepInterchangeFree (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha')

/-! ## The embedding into the combined rewrite -/

/-- The fragment embeds ctor-for-ctor into the combined saturated rewrite: structural steps
through the interchange-free-to-full embedding, triangles and congruences one-to-one. -/
theorem SaturatedStepInterchangeFree.toSaturatedTwoCellStep
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : SaturatedStepInterchangeFree cellA cellB) : SaturatedTwoCellStep cellA cellB := by
  induction step with
  | ofStructural structuralStep =>
      exact SaturatedTwoCellStep.ofFree (twoCellStepInterchangeFree_isTwoCellStep structuralStep)
  | leftBareSnake => exact SaturatedTwoCellStep.leftBareSnake
  | leftSnakePrefix rest => exact SaturatedTwoCellStep.leftSnakePrefix rest
  | rightBareSnake => exact SaturatedTwoCellStep.rightBareSnake
  | rightSnakePrefix rest => exact SaturatedTwoCellStep.rightSnakePrefix rest
  | vcompCongrLeft cellBeta _ innerHypothesis =>
      exact SaturatedTwoCellStep.vcompCongrLeft cellBeta innerHypothesis
  | vcompCongrRight cellAlpha _ innerHypothesis =>
      exact SaturatedTwoCellStep.vcompCongrRight cellAlpha innerHypothesis
  | whiskerLeftCongr oneCell _ innerHypothesis =>
      exact SaturatedTwoCellStep.whiskerLeftCongr oneCell innerHypothesis
  | whiskerRightCongr oneCell _ innerHypothesis =>
      exact SaturatedTwoCellStep.whiskerRightCongr oneCell innerHypothesis

/-! ## Strong normalization — free, by subrelation descent -/

/-- ★ The fragment is strongly normalizing — accessibility descends to a subrelation, so the
combined rewrite's unconditional termination carries over with zero fresh bookkeeping. -/
theorem saturatedStepInterchangeFree_isStronglyNormalizing
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Acc (fun reduct redex => SaturatedStepInterchangeFree redex reduct) cell :=
  accessible_ofSubrelation
    (fun step => step.toSaturatedTwoCellStep)
    (saturatedTwoCellStep_isStronglyNormalizing cell)

/-! ## Soundness for the saturated theory -/

/-- Every fragment step is a saturated convertibility — the normalizer this fragment carries
computes within `SaturatedTwoCellConv`. -/
theorem SaturatedStepInterchangeFree.toSaturatedConv
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (step : SaturatedStepInterchangeFree cellA cellB) : SaturatedTwoCellConv cellA cellB :=
  step.toSaturatedTwoCellStep.toSaturatedConv

/-! ## Honesty marker -/

/-- **Honesty marker — the NF-bearing saturated fragment is SHIPPED.**  The two-layer saturated
normal-form architecture (forced by `interchangeWitness_notLocallyConfluent`: the FULL rewrite
cannot carry unique normal forms) has its layer-one relation: triangles + eleven structural laws,
interchange withdrawn, SN inherited by subrelation descent, sound for `SaturatedTwoCellConv`.
NOT yet shipped: the computable fragment reducer (extending the generic `reduceOnce` with the
four triangle root-recognizers) + its completeness, the fragment's LOCAL confluence (the
triangle × structural critical pairs — the obstructing interchange peak is withdrawn), and the
layer-two delegation of normal-form residual equality to the FREE trace decision.
`fxMode_hasOrientedTraceCanonicalForm` / `fxMode_hasSaturatedRewriteNormalFormDecision` stay
`false` until those land.  `= true`. -/
def fxMode_hasSaturatedInterchangeFreeFragment : Bool := true

end FX1Poly.Polygraph
