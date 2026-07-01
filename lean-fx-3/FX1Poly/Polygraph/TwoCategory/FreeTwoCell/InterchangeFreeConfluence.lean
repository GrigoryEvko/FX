import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFree

/-! # mode-3 floor — confluence of the INTERCHANGE-FREE fragment, reduced to its (TRUE) local confluence

`FreeTwoCellInterchangeFree` shipped the interchange-free fragment `TwoCellStepInterchangeFree` (the eleven
structural laws, Godement step withdrawn) and proved it strongly normalizing. This file closes the Newman half
of the convergence reduction for that fragment, EXACTLY mirroring `FreeTwoCellConfluence` for the full system —
but with a decisive difference in status.

  ★ `twoCellStepInterchangeFree_isConfluent` — the interchange-free fragment is CONFLUENT, GIVEN its local
    confluence; via the abstract zero-axiom `Core.newman` fed the proven SN floor.

Unlike the full `TwoCellStep` (whose `TwoCellLocallyConfluent` is FALSE because of the interchange critical
pair), the interchange-free fragment's local confluence `TwoCellInterchangeFreeLocallyConfluent` is **genuinely
true and dischargeable**: with `interchange` withdrawn, the only divergent peaks are the free-2-category
coherence pairs (pentagon, unit, whisker-distribution), all of which join via the star-congruence toolkit and
`vcompAssoc`. So this Newman reduction is NON-vacuous — it isolates the fragment's convergence to a real,
provable obligation, which is the next brick of the confluence-modulo-interchange route to the fib-3 keystone.

Also ships the **star-congruence toolkit** for the fragment: a many-step `TwoCellStepInterchangeFree` reduction
lifts through each of the four one-hole contexts (left/right whiskering, left/right vertical-composition factor)
— the reflexive-transitive closure of each congruence rule, the join-builder that the local-confluence proof
consumes.

Zero external dependencies beyond `FreeTwoCellInterchangeFree` (which re-exports the Core Newman). Raw Lean 4 +
Init; every theorem `propext`/`Quot.sound`/`Classical`/`sorry`/`omega`-free (`Core.ReflTransClosure` is
`cases`-clean — its indices are free variables; the lifts are structural inductions; the reduction is the
abstract `Core.newman`). -/

namespace FX1Poly.Tier0

/-! ## The star-congruence toolkit for the interchange-free fragment -/

/-- A many-step interchange-free reduction lifts under **left whiskering**. -/
theorem twoCellInterchangeFreeReducesStar_whiskerLeftCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    {cellLow cellHigh : RawTwoCellExpr signature oneCellG oneCellH}
    (chain : Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.whiskerLeft oneCell cellLow) (RawTwoCellExpr.whiskerLeft oneCell cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStepInterchangeFree.whiskerLeftCongr oneCell first) inductionHypothesis

/-- A many-step interchange-free reduction lifts under **right whiskering**. -/
theorem twoCellInterchangeFreeReducesStar_whiskerRightCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {cellLow cellHigh : RawTwoCellExpr signature oneCellF oneCellG}
    (chain : Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.whiskerRight oneCell cellLow) (RawTwoCellExpr.whiskerRight oneCell cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStepInterchangeFree.whiskerRightCongr oneCell first) inductionHypothesis

/-- A many-step interchange-free reduction lifts into the **left factor** of a vertical composite. -/
theorem twoCellInterchangeFreeReducesStar_vcompCongrLeft {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellLow cellHigh : RawTwoCellExpr signature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (chain : Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.vcomp cellLow cellBeta) (RawTwoCellExpr.vcomp cellHigh cellBeta) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStepInterchangeFree.vcompCongrLeft cellBeta first) inductionHypothesis

/-- A many-step interchange-free reduction lifts into the **right factor** of a vertical composite. -/
theorem twoCellInterchangeFreeReducesStar_vcompCongrRight {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellLow cellHigh : RawTwoCellExpr signature oneCellG oneCellH}
    (chain : Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b) cellLow cellHigh) :
    Core.ReflTransClosure (fun a b => TwoCellStepInterchangeFree signature a b)
      (RawTwoCellExpr.vcomp cellAlpha cellLow) (RawTwoCellExpr.vcomp cellAlpha cellHigh) := by
  induction chain with
  | refl _ => exact Core.ReflTransClosure.refl _
  | head first _rest inductionHypothesis =>
      exact Core.ReflTransClosure.head (TwoCellStepInterchangeFree.vcompCongrRight cellAlpha first) inductionHypothesis

/-! ## Newman: convergence of the fragment reduced to its (TRUE) local confluence -/

/-- **Local (weak) confluence of the interchange-free fragment** — at every parallel boundary, divergent single
steps join. Unlike the full system's `TwoCellLocallyConfluent` (false, Godement), this predicate is TRUE: with
`interchange` withdrawn, every critical pair is a free-2-category coherence pair that joins via the star toolkit
and `vcompAssoc`. It is the precise, dischargeable obligation that `twoCellStepInterchangeFree_isConfluent`
reduces the fragment's convergence to. -/
def TwoCellInterchangeFreeLocallyConfluent (signature : ModeSignature) : Prop :=
  ∀ {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode},
    Core.WeaklyConfluent
      (fun (a b : RawTwoCellExpr signature sourcePath targetPath) => TwoCellStepInterchangeFree signature a b)

/-- ★ **The interchange-free fragment is CONFLUENT (Church-Rosser), GIVEN its local confluence.** Newman's lemma
at each parallel boundary: the fragment is strongly normalizing (`twoCellStepInterchangeFree_isStronglyNormalizing`,
itself inherited from the full-system SN), so SN + the supplied local confluence ⟹ confluence. This isolates the
fragment's convergence to EXACTLY `TwoCellInterchangeFreeLocallyConfluent` — and because that obligation is now
genuinely provable (no interchange peak), this is the real convergence backbone of the modulo-interchange route,
not the honest-but-vacuous reduction `FreeTwoCellConfluence` could only offer for the full system. -/
theorem twoCellStepInterchangeFree_isConfluent (signature : ModeSignature)
    (locallyConfluent : TwoCellInterchangeFreeLocallyConfluent signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} :
    Core.Confluent
      (fun (a b : RawTwoCellExpr signature sourcePath targetPath) => TwoCellStepInterchangeFree signature a b) :=
  Core.newman (WellFounded.intro (fun cell => twoCellStepInterchangeFree_isStronglyNormalizing cell)) locallyConfluent

end FX1Poly.Tier0
