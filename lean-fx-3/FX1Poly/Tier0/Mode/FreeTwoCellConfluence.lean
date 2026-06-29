import FX1Poly.Tier0.Mode.FreeTwoCellStrongNormalization
import FX1Poly.Core.Rewriting.Confluence.Newman

/-! # mode-3 floor — confluence of the `TwoCellStep` 3-polygraph, reduced to LOCAL confluence

`FreeTwoCellStrongNormalization` discharged the TERMINATION half of the 3-polygraph convergence
(`twoCellStep_isStronglyNormalizing`). Convergence = termination + confluence, and **Newman's lemma** closes the
gap: a strongly-normalizing, LOCALLY (weakly) confluent relation is CONFLUENT (Church-Rosser). The abstract,
zero-axiom Newman already lives in `FX1Poly/Core/Rewriting/Confluence/Newman.lean` (`Core.newman`), over an
arbitrary `Carrier → Carrier → Prop` with its own reflexive-transitive closure `Core.ReflTransClosure`.

`TwoCellStep` PRESERVES its parallel boundary `(sourcePath, targetPath)` (every rule rewrites a cell to a cell
of the same 1-cell source and target), so it instantiates the abstract relation **fibre-wise**: at a fixed
boundary, `Carrier := RawTwoCellExpr signature sourcePath targetPath` and `rel := TwoCellStep signature` is a
genuine binary relation on that `Carrier`. Feeding `twoCellStep_isStronglyNormalizing` as the `WellFounded`
witness, this file proves:

  ★ **`twoCellStep_isConfluent` — the `TwoCellStep` 3-polygraph is CONFLUENT, GIVEN local confluence.**

This is the exact analogue of `AdjunctionSaturatedNormalization` reducing saturated SN to the structural floor:
it isolates the remaining convergence obligation to EXACTLY `TwoCellLocallyConfluent` (weak confluence — every
divergent pair of single steps joins), i.e. the critical-pair analysis of the twelve rules (the `vcompAssoc`
critical pairs already join in `AdjunctionTriangleObstruction`; the open content is the interchange/Godement
critical pair). Discharging that one obligation flips `fxMode_hasConvergentThreeCellSystem` and cascades up to
the fib-3 keystone `fxMode_hasModeRelativeConvDecision`.

Also ships the **star-congruence toolkit** local confluence consumes: a many-step `TwoCellStep` reduction lifts
through each of the four one-hole contexts (left/right whiskering, left/right vertical-composition factor) — the
reflexive-transitive closure of each congruence rule.

Zero external dependencies beyond `FreeTwoCellStrongNormalization` + the Core Newman. Raw Lean 4 + Init; every
theorem `propext`/`Quot.sound`/`Classical`/`sorry`/`omega`-free (`Core.ReflTransClosure` is `cases`-clean — its
indices are free variables; the lifts are structural inductions; the reduction is the abstract `Core.newman`). -/

namespace FX1Poly.Tier0

/-! ## The star-congruence toolkit — a many-step reduction lifts through each one-hole context -/

/-- A many-step `TwoCellStep` reduction lifts under **left whiskering**: reduce the whiskered 2-cell by
reducing the whiskerand, step for step (each step via `TwoCellStep.whiskerLeftCongr`). -/
theorem twoCellReducesStar_whiskerLeftCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    {cellLow cellHigh : RawTwoCellExpr signature oneCellG oneCellH}
    (chain : Core.ReflTransClosure (fun a b => TwoCellStep signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStep signature a b)
      (RawTwoCellExpr.whiskerLeft oneCell cellLow) (RawTwoCellExpr.whiskerLeft oneCell cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStep.whiskerLeftCongr oneCell first) inductionHypothesis

/-- A many-step `TwoCellStep` reduction lifts under **right whiskering**. -/
theorem twoCellReducesStar_whiskerRightCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {cellLow cellHigh : RawTwoCellExpr signature oneCellF oneCellG}
    (chain : Core.ReflTransClosure (fun a b => TwoCellStep signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStep signature a b)
      (RawTwoCellExpr.whiskerRight oneCell cellLow) (RawTwoCellExpr.whiskerRight oneCell cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStep.whiskerRightCongr oneCell first) inductionHypothesis

/-- A many-step `TwoCellStep` reduction lifts into the **left factor** of a vertical composite (right factor
fixed). -/
theorem twoCellReducesStar_vcompCongrLeft {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellLow cellHigh : RawTwoCellExpr signature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (chain : Core.ReflTransClosure (fun a b => TwoCellStep signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStep signature a b)
      (RawTwoCellExpr.vcomp cellLow cellBeta) (RawTwoCellExpr.vcomp cellHigh cellBeta) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStep.vcompCongrLeft cellBeta first) inductionHypothesis

/-- A many-step `TwoCellStep` reduction lifts into the **right factor** of a vertical composite (left factor
fixed). -/
theorem twoCellReducesStar_vcompCongrRight {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellLow cellHigh : RawTwoCellExpr signature oneCellG oneCellH}
    (chain : Core.ReflTransClosure (fun a b => TwoCellStep signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStep signature a b)
      (RawTwoCellExpr.vcomp cellAlpha cellLow) (RawTwoCellExpr.vcomp cellAlpha cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStep.vcompCongrRight cellAlpha first) inductionHypothesis

/-! ## Newman: convergence reduced to LOCAL confluence -/

/-- **Local (weak) confluence of `TwoCellStep`** — at every parallel boundary, divergent single steps join.
This is the one remaining convergence obligation (the critical-pair analysis of the twelve rules); discharging
it makes `twoCellStep_isConfluent` unconditional and flips `fxMode_hasConvergentThreeCellSystem`. -/
def TwoCellLocallyConfluent (signature : ModeSignature) : Prop :=
  ∀ {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode},
    Core.WeaklyConfluent (fun (a b : RawTwoCellExpr signature sourcePath targetPath) => TwoCellStep signature a b)

/-- ★ **The `TwoCellStep` 3-polygraph is CONFLUENT (Church-Rosser), GIVEN local confluence.**  Newman's lemma at
each parallel boundary: `TwoCellStep` is strongly normalizing (`twoCellStep_isStronglyNormalizing`, packaged as
the `WellFounded` of the flipped step), so SN + the supplied local confluence ⟹ confluence — divergent many-step
reductions join. This isolates the remaining convergence ingredient to EXACTLY `TwoCellLocallyConfluent`, exactly
as `AdjunctionSaturated*` isolated termination to the structural floor. -/
theorem twoCellStep_isConfluent (signature : ModeSignature)
    (locallyConfluent : TwoCellLocallyConfluent signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} :
    Core.Confluent (fun (a b : RawTwoCellExpr signature sourcePath targetPath) => TwoCellStep signature a b) :=
  Core.newman (WellFounded.intro (fun cell => twoCellStep_isStronglyNormalizing cell)) locallyConfluent

end FX1Poly.Tier0
