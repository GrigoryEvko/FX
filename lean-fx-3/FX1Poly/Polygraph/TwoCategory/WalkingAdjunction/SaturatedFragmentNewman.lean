import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedFragmentNormalize
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable

/-! # SaturatedFragmentNewman — the fragment's Newman interface + conditional word-problem decision (SAT-NF brick D1)

The fragment normalizer (brick C) computes normal forms without confluence; UNIQUENESS of those
normal forms — and hence the rewrite-route decision of the fragment's equational theory — needs
exactly one more ingredient: the fragment's LOCAL confluence.  Unlike the full saturated rewrite
(whose local confluence is FALSE — the Godement interchange peak, `SaturatedConvergence`), the
interchange-free fragment's local confluence is genuinely true: interchange is withdrawn, and the
remaining peaks are the free-2-category coherence pairs plus the four triangle × `vcompAssoc`
pairs already joined in `SaturatedConvergence`.  This file ships the INTERFACE that discharge
plugs into, exactly mirroring `InterchangeFreeConfluence` for the structural fragment:

  * the **star-congruence toolkit** — a many-step fragment reduction lifts through each of the
    four one-hole contexts (the join-builder the peak analysis consumes);
  * `SaturatedInterchangeFreeLocallyConfluent` — the precise open obligation;
  * `saturatedStepInterchangeFree_isConfluent` — Newman: SN (shipped) + local confluence ⟹
    confluence;
  * ★ `decidableSaturatedFragmentEquational` — Knuth-Bendix: given local confluence, the
    fragment's equational theory is DECIDED by the brick-C normalizer (normalize both, compare
    under the hand-rolled `DecidableEq`);
  * `saturatedFragmentNormalize_isCanonical` — given local confluence, the normalizer's output
    is THE canonical representative (unique normal form).

HONESTY: everything below `SaturatedInterchangeFreeLocallyConfluent` is CONDITIONAL on it; the
discharge (the triangle × structural and structural × structural peak analysis) is the remaining
SAT-NF work (bricks D2+).  Markers stay until the unconditional decision lands. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The star-congruence toolkit for the saturated fragment -/

/-- A many-step fragment reduction lifts under **left whiskering**. -/
theorem saturatedInterchangeFreeReducesStar_whiskerLeftCongr
    {sourceMode middleMode targetMode : AdjunctionMode}
    (oneCell : ModalityPath adjunctionGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath adjunctionGraph middleMode targetMode}
    {cellLow cellHigh : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH}
    (chain : Core.ReflTransClosure
      (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB) cellLow cellHigh) :
    Core.ReflTransClosure (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB)
      (RawTwoCellExpr.whiskerLeft oneCell cellLow) (RawTwoCellExpr.whiskerLeft oneCell cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head
        (SaturatedStepInterchangeFree.whiskerLeftCongr oneCell first) inductionHypothesis

/-- A many-step fragment reduction lifts under **right whiskering**. -/
theorem saturatedInterchangeFreeReducesStar_whiskerRightCongr
    {sourceMode middleMode targetMode : AdjunctionMode}
    {oneCellF oneCellG : ModalityPath adjunctionGraph sourceMode middleMode}
    (oneCell : ModalityPath adjunctionGraph middleMode targetMode)
    {cellLow cellHigh : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
    (chain : Core.ReflTransClosure
      (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB) cellLow cellHigh) :
    Core.ReflTransClosure (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB)
      (RawTwoCellExpr.whiskerRight oneCell cellLow) (RawTwoCellExpr.whiskerRight oneCell cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head
        (SaturatedStepInterchangeFree.whiskerRightCongr oneCell first) inductionHypothesis

/-- A many-step fragment reduction lifts into the **left factor** of a vertical composite. -/
theorem saturatedInterchangeFreeReducesStar_vcompCongrLeft
    {sourceMode targetMode : AdjunctionMode}
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellLow cellHigh : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH)
    (chain : Core.ReflTransClosure
      (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB) cellLow cellHigh) :
    Core.ReflTransClosure (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB)
      (RawTwoCellExpr.vcomp cellLow cellBeta) (RawTwoCellExpr.vcomp cellHigh cellBeta) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head
        (SaturatedStepInterchangeFree.vcompCongrLeft cellBeta first) inductionHypothesis

/-- A many-step fragment reduction lifts into the **right factor** of a vertical composite. -/
theorem saturatedInterchangeFreeReducesStar_vcompCongrRight
    {sourceMode targetMode : AdjunctionMode}
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG)
    {cellLow cellHigh : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH}
    (chain : Core.ReflTransClosure
      (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB) cellLow cellHigh) :
    Core.ReflTransClosure (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB)
      (RawTwoCellExpr.vcomp cellAlpha cellLow) (RawTwoCellExpr.vcomp cellAlpha cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head
        (SaturatedStepInterchangeFree.vcompCongrRight cellAlpha first) inductionHypothesis

/-! ## Newman: the fragment's convergence reduced to its (TRUE, open) local confluence -/

/-- **Local (weak) confluence of the saturated interchange-free fragment** — at every parallel
boundary, divergent single fragment steps join.  Unlike the full saturated rewrite's
`SaturatedTwoCellLocallyConfluent` (FALSE — Godement), this predicate is genuinely true:
interchange is withdrawn, and the remaining peaks are the structural coherence pairs plus the
four triangle × `vcompAssoc` pairs (already joined as `saturated*AssocCriticalPair_joins`).
The OPEN obligation the SAT-NF peak analysis (bricks D2+) discharges. -/
def SaturatedInterchangeFreeLocallyConfluent : Prop :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode},
    Core.WeaklyConfluent
      (fun (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) =>
        SaturatedStepInterchangeFree cellA cellB)

/-- ★ **The fragment is CONFLUENT (Church-Rosser), GIVEN its local confluence.**  Newman's lemma
at each parallel boundary over the shipped strong normalization. -/
theorem saturatedStepInterchangeFree_isConfluent
    (locallyConfluent : SaturatedInterchangeFreeLocallyConfluent)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} :
    Core.Confluent
      (fun (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) =>
        SaturatedStepInterchangeFree cellA cellB) :=
  Core.newman
    (WellFounded.intro (fun cell => saturatedStepInterchangeFree_isStronglyNormalizing cell))
    locallyConfluent

/-! ## Knuth-Bendix: the conditional word-problem decision + canonicity -/

/-- ★ **Knuth-Bendix at the fragment**: given local confluence, the fragment's equational theory
is DECIDED by the brick-C normalizer — normalize both sides, compare normal forms under the
hand-rolled decidable equality of adjunction 2-cell expressions. -/
def decidableSaturatedFragmentEquational
    (locallyConfluent : SaturatedInterchangeFreeLocallyConfluent)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :
    Decidable (Core.EquationalTheory
      (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB) cellFirst cellSecond) :=
  letI : DecidableEq (RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) :=
    adjunctionRawTwoCellDecidableEq
  Core.knuthBendixDecidesWordProblem
    (WellFounded.intro (fun cell => saturatedStepInterchangeFree_isStronglyNormalizing cell))
    locallyConfluent
    (saturatedFragmentNormalizer sourcePath targetPath)
    cellFirst cellSecond

/-- **The normalizer's output is THE canonical representative, given local confluence**: any
fragment-convertible normal form IS the computed normal form — unique normal forms. -/
theorem saturatedFragmentNormalize_isCanonical
    (locallyConfluent : SaturatedInterchangeFreeLocallyConfluent)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell canonical : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (convertible : Core.EquationalTheory
      (fun cellA cellB => SaturatedStepInterchangeFree cellA cellB) cell canonical)
    (canonicalIsNormal : ∀ next, ¬ SaturatedStepInterchangeFree canonical next) :
    (saturatedFragmentNormalizer sourcePath targetPath).normalize cell = canonical :=
  (saturatedFragmentNormalizer sourcePath targetPath).normalize_isCanonical
    (saturatedStepInterchangeFree_isConfluent locallyConfluent) convertible canonicalIsNormal

end FX1Poly.Polygraph
