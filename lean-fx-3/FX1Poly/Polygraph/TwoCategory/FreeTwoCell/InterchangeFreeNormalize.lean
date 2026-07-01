import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeLocalConfluence
import FX1Poly.Polygraph.Rewriting.Confluence.ConvergentNormalizerOfReducer

/-! # mode-3 floor — the COMPUTABLE normalizer of the interchange-free fragment + decidable interchange-free
2-cell convertibility

`FreeTwoCellInterchangeFreeLocalConfluence` shipped the two abstract halves of the interchange-free fragment's
convergence: it is strongly normalizing (`twoCellStepInterchangeFree_isStronglyNormalizing`, inherited from the
full-system SN) and confluent unconditionally (`twoCellStepInterchangeFree_isConfluentUnconditional`, the just-
discharged local confluence fed to Newman).  Those are EXISTENCE facts about the rewrite relation; they do not by
themselves compute a normal form.  This file turns them into a real DECISION:

  ★ `RawTwoCellExpr.reduceOnce` — a computable, deterministic, leftmost-outermost one-step redex finder for the
    eleven interchange-free rules.  Built from three non-recursive root probes (`reduceRootVcomp`,
    `reduceRootWhiskerLeft`, `reduceRootWhiskerRight`, plus the `dropRightIdentity` id-right helper) and a
    structural recursion that, after the root probe misses, descends into the leftmost reducible factor.
  ★ `RawTwoCellExpr.reduceOnce_sound` — every fired redex is a genuine `TwoCellStepInterchangeFree` step.
  ★ `RawTwoCellExpr.reduceOnce_complete` — where the reducer halts (`= none`), no interchange-free step leaves the
    cell: it is a normal form (progress, the contrapositive `reduceOnce_ne_none_of_step` by induction on a step).
  ★ `interchangeFreeNormalizer` — the `Core.ConvergentNormalizer` for the fragment, built GENERICALLY by
    `Core.ConvergentNormalizer.ofReducer`: it large-eliminates the shipped strong-normalization `Acc` witness with
    `Acc.rec` (NOT `WellFounded.fix` — axiom-free), firing `reduceOnce` until it halts.  So the normal-form
    function is now DATA, not merely promised by termination.
  ★ `interchangeFreeConv_iff_normalFormEq` — the headline: two free 2-cells are interchange-free CONVERTIBLE
    (`Core.EquationalTheory` of the fragment step — the symmetric-reflexive-transitive closure) IFF they have the
    SAME normal form.  This is the Knuth–Bendix word-problem reduction `ConvergentNormalizer.equationalTheory_iff`
    fed the shipped unconditional confluence — Church–Rosser composed with normal-form uniqueness.

It also lands the SOUND POSITIVE HALF of the FULL strict-2-category 2-cell decision (`TwoCellConv`, the gate's
target — the equivalence closure of the FULL `TwoCellStep`, Godement `interchange` INCLUDED):

  ★ `interchangeFreeConv_imp_twoCellConv` / `normalFormEq_imp_twoCellConv` — equal interchange-free normal forms
    imply FULL convertibility (every withdrawn-fragment step is still a `TwoCellStep`, hence a `TwoCellConv`).  So
    the convergent normalizer SOUNDLY decides the YES direction of full 2-cell equality.  Together with the shipped
    SOUND NEGATIVE half (`TwoCellConv.not_of_generatorCount_ne` in `ComputadWordProblem`: distinct generator counts
    ⟹ not convertible), the full `TwoCellConv` decision is reduced to EXACTLY the modulo-interchange cases —
    distinct interchange-free normal forms with EQUAL generator count, the genuine Godement ambiguity.

This is the convergence floor of the confluence-modulo-interchange route to the fib-3 keystone: it decides 2-cell
equality UP TO the structural eleven laws (with the Godement `interchange` equation withdrawn).  The remaining
brick toward the full `fxMode_hasModeRelativeConvDecision` flip is deciding the resulting normal forms MODULO the
withdrawn interchange equation (and a `DecidableEq` on the indexed free-2-cell expressions to turn the
interchange-free iff into a literal `Decidable`, blocked by the whisker-split `composePath` ambiguity) — both
honest next steps, not discharged here.

Reuses the GENERIC engines `Core.ConvergentNormalizer.ofReducer` (Acc.rec normalizer) and
`Core.ConvergentNormalizer.equationalTheory_iff` (the abstract Knuth–Bendix decision); the fragment-specific work
is the reducer and its soundness/completeness.  Raw Lean 4 + Init; every declaration
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the reducer is structural recursion with
full constructor enumeration — the id-right probe is factored to FREE boundary indices so its catch-all never
refines a `composePath`-shaped index; the proofs are `nomatch` / `Option.some.inj` / `split` on the reducer
results).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

/-! ## The deterministic one-step reducer

`reduceOnce` fires a single interchange-free redex root-first, then descends into the leftmost reducible factor.
The three ROOT probes below are non-recursive and use FULL constructor enumeration (never a wildcard over the
indexed cell, which would leak `propext`); the recursion lives only in `reduceOnce`. -/

/-- Drop a right identity: `cellAlpha ⊟ id ⟶ cellAlpha` when `cellBeta` is an identity, else `none`.  Factored
out with FREE boundary indices so the catch-all over `cellBeta` never refines a `composePath`-shaped index — the
caller (`reduceRootVcomp`) has often already pinned `cellBeta`'s source to a `composePath`, which an inline
catch-all would force the dependent matcher to unify two `composePath`s over. -/
def RawTwoCellExpr.dropRightIdentity {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    Option (RawTwoCellExpr signature oneCellF oneCellH) :=
  match cellBeta with
  | .id _ => some cellAlpha
  | .gen _ => none
  | .vcomp _ _ => none
  | .whiskerLeft _ _ => none
  | .whiskerRight _ _ => none

/-- Fire one of the three VCOMP root redexes (`vcompIdLeft`, `vcompAssoc`, `vcompIdRight`) on `vcomp α β`, or
`none` if the root is not a vcomp redex.  Non-recursive; the id-right probe is `dropRightIdentity`. -/
def RawTwoCellExpr.reduceRootVcomp {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    Option (RawTwoCellExpr signature oneCellF oneCellH) :=
  match cellAlpha with
  | .id _ => some cellBeta
  | .vcomp cellAlphaLeft cellAlphaRight =>
      some (.vcomp cellAlphaLeft (.vcomp cellAlphaRight cellBeta))
  | .gen genAlpha => RawTwoCellExpr.dropRightIdentity (.gen genAlpha) cellBeta
  | .whiskerLeft oneCellAlpha bodyAlpha =>
      RawTwoCellExpr.dropRightIdentity (.whiskerLeft oneCellAlpha bodyAlpha) cellBeta
  | .whiskerRight oneCellAlpha bodyAlpha =>
      RawTwoCellExpr.dropRightIdentity (.whiskerRight oneCellAlpha bodyAlpha) cellBeta

/-- Fire one of the two LEFT-WHISKER root redexes (`whiskerLeftId`, `whiskerLeftVcomp`) on `oneCell ◁ body`, or
`none` otherwise.  Non-recursive — full constructor enumeration over `body` (free body indices, so clean). -/
def RawTwoCellExpr.reduceRootWhiskerLeft {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {bodyDom bodyCod : ModalityPath signature.graph middleMode targetMode}
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    Option (RawTwoCellExpr signature (composePath oneCell bodyDom) (composePath oneCell bodyCod)) :=
  match body with
  | .id path => some (.id (composePath oneCell path))
  | .vcomp bodyLeft bodyRight =>
      some (.vcomp (.whiskerLeft oneCell bodyLeft) (.whiskerLeft oneCell bodyRight))
  | .gen _ => none
  | .whiskerLeft _ _ => none
  | .whiskerRight _ _ => none

/-- Fire one of the two RIGHT-WHISKER root redexes (`whiskerRightId`, `whiskerRightVcomp`) on `body ▷ oneCell`,
or `none` otherwise.  Non-recursive — full constructor enumeration over `body`. -/
def RawTwoCellExpr.reduceRootWhiskerRight {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {bodyDom bodyCod : ModalityPath signature.graph sourceMode middleMode}
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    Option (RawTwoCellExpr signature (composePath bodyDom oneCell) (composePath bodyCod oneCell)) :=
  match body with
  | .id path => some (.id (composePath path oneCell))
  | .vcomp bodyLeft bodyRight =>
      some (.vcomp (.whiskerRight oneCell bodyLeft) (.whiskerRight oneCell bodyRight))
  | .gen _ => none
  | .whiskerLeft _ _ => none
  | .whiskerRight _ _ => none

/-- ★ Fire one interchange-free redex (root-first, then the leftmost reducible factor), or `none` at a normal
form.  Structural recursion on the cell; the root probes are the non-recursive helpers above.  A vcomp tries its
root redexes, then a step in the left factor, then a step in the right factor; a whisker tries its root redexes,
then a step in its body; generators and identities are normal. -/
def RawTwoCellExpr.reduceOnce {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath →
    Option (RawTwoCellExpr signature sourcePath targetPath)
  | _, _, _, _, .gen _ => none
  | _, _, _, _, .id _ => none
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      match cellAlpha.reduceRootVcomp cellBeta with
      | some rootReduct => some rootReduct
      | none =>
          match cellAlpha.reduceOnce with
          | some alphaReduct => some (.vcomp alphaReduct cellBeta)
          | none =>
              match cellBeta.reduceOnce with
              | some betaReduct => some (.vcomp cellAlpha betaReduct)
              | none => none
  | _, _, _, _, .whiskerLeft oneCell body =>
      match RawTwoCellExpr.reduceRootWhiskerLeft oneCell body with
      | some rootReduct => some rootReduct
      | none =>
          match body.reduceOnce with
          | some bodyReduct => some (.whiskerLeft oneCell bodyReduct)
          | none => none
  | _, _, _, _, .whiskerRight oneCell body =>
      match RawTwoCellExpr.reduceRootWhiskerRight oneCell body with
      | some rootReduct => some rootReduct
      | none =>
          match body.reduceOnce with
          | some bodyReduct => some (.whiskerRight oneCell bodyReduct)
          | none => none

/-! ## Soundness: every fired redex is a genuine interchange-free step -/

/-- Soundness of the id-right probe: a `some` from `dropRightIdentity` is the `vcompIdRight` step. -/
theorem RawTwoCellExpr.dropRightIdentity_sound {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha : RawTwoCellExpr signature oneCellF oneCellG}
    {cellBeta : RawTwoCellExpr signature oneCellG oneCellH}
    {reduct : RawTwoCellExpr signature oneCellF oneCellH}
    (fired : cellAlpha.dropRightIdentity cellBeta = some reduct) :
    TwoCellStepInterchangeFree signature (RawTwoCellExpr.vcomp cellAlpha cellBeta) reduct := by
  cases cellBeta with
  | id pathId =>
      exact (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.vcompIdRight cellAlpha
  | gen _ => nomatch fired
  | vcomp _ _ => nomatch fired
  | whiskerLeft _ _ => nomatch fired
  | whiskerRight _ _ => nomatch fired

/-- Soundness of the vcomp root probe: a `some` is `vcompIdLeft`, `vcompAssoc`, or `vcompIdRight`. -/
theorem RawTwoCellExpr.reduceRootVcomp_sound {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha : RawTwoCellExpr signature oneCellF oneCellG}
    {cellBeta : RawTwoCellExpr signature oneCellG oneCellH}
    {reduct : RawTwoCellExpr signature oneCellF oneCellH}
    (fired : cellAlpha.reduceRootVcomp cellBeta = some reduct) :
    TwoCellStepInterchangeFree signature (RawTwoCellExpr.vcomp cellAlpha cellBeta) reduct := by
  cases cellAlpha with
  | id pathId =>
      exact (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.vcompIdLeft cellBeta
  | vcomp cellAlphaLeft cellAlphaRight =>
      exact (Option.some.inj fired) ▸
        TwoCellStepInterchangeFree.vcompAssoc cellAlphaLeft cellAlphaRight cellBeta
  | gen genAlpha => exact RawTwoCellExpr.dropRightIdentity_sound fired
  | whiskerLeft oneCellAlpha bodyAlpha => exact RawTwoCellExpr.dropRightIdentity_sound fired
  | whiskerRight oneCellAlpha bodyAlpha => exact RawTwoCellExpr.dropRightIdentity_sound fired

/-- Soundness of the left-whisker root probe: a `some` is `whiskerLeftId` or `whiskerLeftVcomp`.  Term-mode match
on `body` so the `id`-case path binder is reliable (a tactic `cases` drops it under the double-index unification). -/
theorem RawTwoCellExpr.reduceRootWhiskerLeft_sound {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode) :
    {bodyDom bodyCod : ModalityPath signature.graph middleMode targetMode} →
    (body : RawTwoCellExpr signature bodyDom bodyCod) →
    {reduct : RawTwoCellExpr signature (composePath oneCell bodyDom) (composePath oneCell bodyCod)} →
    RawTwoCellExpr.reduceRootWhiskerLeft oneCell body = some reduct →
    TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerLeft oneCell body) reduct
  | _, _, .id pathBody, _, fired =>
      (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.whiskerLeftId oneCell pathBody
  | _, _, .vcomp bodyLeft bodyRight, _, fired =>
      (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.whiskerLeftVcomp oneCell bodyLeft bodyRight
  | _, _, .gen _, _, fired => nomatch fired
  | _, _, .whiskerLeft _ _, _, fired => nomatch fired
  | _, _, .whiskerRight _ _, _, fired => nomatch fired

/-- Soundness of the right-whisker root probe: a `some` is `whiskerRightId` or `whiskerRightVcomp`. -/
theorem RawTwoCellExpr.reduceRootWhiskerRight_sound {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode) :
    {bodyDom bodyCod : ModalityPath signature.graph sourceMode middleMode} →
    (body : RawTwoCellExpr signature bodyDom bodyCod) →
    {reduct : RawTwoCellExpr signature (composePath bodyDom oneCell) (composePath bodyCod oneCell)} →
    RawTwoCellExpr.reduceRootWhiskerRight oneCell body = some reduct →
    TwoCellStepInterchangeFree signature (RawTwoCellExpr.whiskerRight oneCell body) reduct
  | _, _, .id pathBody, _, fired =>
      (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.whiskerRightId pathBody oneCell
  | _, _, .vcomp bodyLeft bodyRight, _, fired =>
      (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.whiskerRightVcomp oneCell bodyLeft bodyRight
  | _, _, .gen _, _, fired => nomatch fired
  | _, _, .whiskerLeft _ _, _, fired => nomatch fired
  | _, _, .whiskerRight _ _, _, fired => nomatch fired

/-- ★ **The reducer is SOUND.**  Every reduct it produces is a genuine one-step interchange-free rewrite.  By
structural recursion on the cell: root redexes ride the three root-probe soundness lemmas; the leftmost-factor
descent rides a congruence constructor over the recursive soundness call. -/
theorem RawTwoCellExpr.reduceOnce_sound {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    {cell reduct : RawTwoCellExpr signature sourcePath targetPath} →
    cell.reduceOnce = some reduct →
    TwoCellStepInterchangeFree signature cell reduct
  | _, _, _, _, .gen _, _, fired => nomatch fired
  | _, _, _, _, .id _, _, fired => nomatch fired
  | _, _, _, _, .vcomp cellAlpha cellBeta, reduct, fired => by
      dsimp only [RawTwoCellExpr.reduceOnce] at fired
      cases hRoot : cellAlpha.reduceRootVcomp cellBeta with
      | some rootReduct =>
          rw [hRoot] at fired
          exact (Option.some.inj fired) ▸ RawTwoCellExpr.reduceRootVcomp_sound hRoot
      | none =>
          rw [hRoot] at fired
          cases hAlpha : cellAlpha.reduceOnce with
          | some alphaReduct =>
              rw [hAlpha] at fired
              exact (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.vcompCongrLeft cellBeta
                (RawTwoCellExpr.reduceOnce_sound hAlpha)
          | none =>
              rw [hAlpha] at fired
              cases hBeta : cellBeta.reduceOnce with
              | some betaReduct =>
                  rw [hBeta] at fired
                  exact (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.vcompCongrRight cellAlpha
                    (RawTwoCellExpr.reduceOnce_sound hBeta)
              | none => rw [hBeta] at fired; nomatch fired
  | _, _, _, _, .whiskerLeft oneCell body, reduct, fired => by
      dsimp only [RawTwoCellExpr.reduceOnce] at fired
      cases hRoot : RawTwoCellExpr.reduceRootWhiskerLeft oneCell body with
      | some rootReduct =>
          rw [hRoot] at fired
          exact (Option.some.inj fired) ▸ RawTwoCellExpr.reduceRootWhiskerLeft_sound oneCell body hRoot
      | none =>
          rw [hRoot] at fired
          cases hBody : body.reduceOnce with
          | some bodyReduct =>
              rw [hBody] at fired
              exact (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.whiskerLeftCongr oneCell
                (RawTwoCellExpr.reduceOnce_sound hBody)
          | none => rw [hBody] at fired; nomatch fired
  | _, _, _, _, .whiskerRight oneCell body, reduct, fired => by
      dsimp only [RawTwoCellExpr.reduceOnce] at fired
      cases hRoot : RawTwoCellExpr.reduceRootWhiskerRight oneCell body with
      | some rootReduct =>
          rw [hRoot] at fired
          exact (Option.some.inj fired) ▸ RawTwoCellExpr.reduceRootWhiskerRight_sound oneCell body hRoot
      | none =>
          rw [hRoot] at fired
          cases hBody : body.reduceOnce with
          | some bodyReduct =>
              rw [hBody] at fired
              exact (Option.some.inj fired) ▸ TwoCellStepInterchangeFree.whiskerRightCongr oneCell
                (RawTwoCellExpr.reduceOnce_sound hBody)
          | none => rw [hBody] at fired; nomatch fired

/-! ## Completeness: a halted reducer marks a normal form (no outgoing step) -/

/-- A right-identity vcomp always presents a root redex (id-left, associativity, or id-right), whatever the left
factor is — so the root probe never returns `none` on it.  Closes the `vcompIdRight` case of progress. -/
theorem RawTwoCellExpr.reduceRootVcomp_rightId_ne_none {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG) :
    cellAlpha.reduceRootVcomp (RawTwoCellExpr.id oneCellG) ≠ none := by
  cases cellAlpha <;> exact fun h => nomatch h

/-- **Progress.**  A cell that admits an interchange-free step is reducible — `reduceOnce` does not return `none`.
By induction on the step: every redex constructor drives `reduceOnce` to a `some` (root redexes via the root
probes, congruences via the inductive hypothesis on the descended factor, dispatched by `split`). -/
theorem RawTwoCellExpr.reduceOnce_ne_none_of_step {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {source target : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStepInterchangeFree signature source target) :
    source.reduceOnce ≠ none := by
  induction step with
  | vcompIdLeft cellAlpha => exact fun h => nomatch h
  | vcompIdRight cellAlpha =>
      intro h
      dsimp only [RawTwoCellExpr.reduceOnce] at h
      cases hRoot : cellAlpha.reduceRootVcomp (RawTwoCellExpr.id _) with
      | some _ => rw [hRoot] at h; exact nomatch h
      | none => exact RawTwoCellExpr.reduceRootVcomp_rightId_ne_none cellAlpha hRoot
  | vcompAssoc cellAlpha cellBeta cellGamma => exact fun h => nomatch h
  | whiskerLeftId oneCell path => exact fun h => nomatch h
  | whiskerRightId path oneCell => exact fun h => nomatch h
  | whiskerLeftVcomp oneCell cellBeta cellGamma => exact fun h => nomatch h
  | whiskerRightVcomp oneCell cellAlpha cellBeta => exact fun h => nomatch h
  | vcompCongrLeft cellBeta innerStep ih =>
      intro h
      dsimp only [RawTwoCellExpr.reduceOnce] at h
      split at h
      · exact nomatch h
      · next hRoot =>
          split at h
          · exact nomatch h
          · next hAlpha => exact ih hAlpha
  | vcompCongrRight cellAlpha innerStep ih =>
      intro h
      dsimp only [RawTwoCellExpr.reduceOnce] at h
      split at h
      · exact nomatch h
      · next hRoot =>
          split at h
          · exact nomatch h
          · next hAlpha =>
              split at h
              · exact nomatch h
              · next hBeta => exact ih hBeta
  | whiskerLeftCongr oneCell innerStep ih =>
      intro h
      dsimp only [RawTwoCellExpr.reduceOnce] at h
      split at h
      · exact nomatch h
      · next hRoot =>
          split at h
          · exact nomatch h
          · next hBody => exact ih hBody
  | whiskerRightCongr oneCell innerStep ih =>
      intro h
      dsimp only [RawTwoCellExpr.reduceOnce] at h
      split at h
      · exact nomatch h
      · next hRoot =>
          split at h
          · exact nomatch h
          · next hBody => exact ih hBody

/-- ★ **The reducer is COMPLETE.**  Where it halts (`reduceOnce = none`), the cell is a normal form — no
interchange-free step leaves it.  Contrapositive of `reduceOnce_ne_none_of_step`. -/
theorem RawTwoCellExpr.reduceOnce_complete {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cell : RawTwoCellExpr signature sourcePath targetPath}
    (halted : cell.reduceOnce = none) :
    ∀ next, ¬ TwoCellStepInterchangeFree signature cell next :=
  fun _next step => RawTwoCellExpr.reduceOnce_ne_none_of_step step halted

/-! ## The convergent normalizer + interchange-free convertibility as normal-form equality -/

/-- ★ **The interchange-free fragment's convergent normalizer.**  Built GENERICALLY by
`Core.ConvergentNormalizer.ofReducer`: it iterates `reduceOnce` along the shipped strong-normalization `Acc`
witness with `Acc.rec` (the well-founded recursion PRIMITIVE — axiom-free, NOT `WellFounded.fix`), halting at the
fragment normal form.  The reducer's soundness keeps each fired step real (so the successor stays accessible — the
descent) and its completeness halts exactly at irreducible cells.  Parameterised by the boundary 1-cells, so the
carrier is the fixed-boundary 2-cell type the abstract engine expects. -/
def interchangeFreeNormalizer (signature : ModeSignature)
    {sourceMode targetMode : signature.graph.Mode}
    (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) :
    Core.ConvergentNormalizer
      (fun (a b : RawTwoCellExpr signature sourcePath targetPath) =>
        TwoCellStepInterchangeFree signature a b) :=
  Core.ConvergentNormalizer.ofReducer
    RawTwoCellExpr.reduceOnce
    (fun fired => RawTwoCellExpr.reduceOnce_sound fired)
    (fun halted next => RawTwoCellExpr.reduceOnce_complete halted next)
    (fun cell => twoCellStepInterchangeFree_isStronglyNormalizing cell)

/-- ★ **Interchange-free convertibility IS normal-form equality.**  Two free 2-cells are convertible by the
interchange-free fragment (`Core.EquationalTheory` of the step — its symmetric-reflexive-transitive closure) IFF
they share a normal form.  The abstract Knuth–Bendix word-problem reduction
(`ConvergentNormalizer.equationalTheory_iff`) fed the shipped unconditional confluence
(`twoCellStepInterchangeFree_isConfluentUnconditional`): Church–Rosser composed with normal-form uniqueness.  The
convergence floor of the modulo-interchange route — it decides 2-cell equality up to the eleven structural laws
(Godement `interchange` withdrawn). -/
theorem interchangeFreeConv_iff_normalFormEq (signature : ModeSignature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) :
    Core.EquationalTheory (fun a b => TwoCellStepInterchangeFree signature a b) cellFirst cellSecond ↔
      (interchangeFreeNormalizer signature sourcePath targetPath).normalize cellFirst =
        (interchangeFreeNormalizer signature sourcePath targetPath).normalize cellSecond :=
  (interchangeFreeNormalizer signature sourcePath targetPath).equationalTheory_iff
    (twoCellStepInterchangeFree_isConfluentUnconditional signature)

/-! ## The sound positive half of the FULL strict-2-category 2-cell decision

The gate `fxMode_hasModeRelativeConvDecision` decides `TwoCellConv` — the equivalence closure of the FULL
`TwoCellStep`, with Godement `interchange` INCLUDED.  Interchange-free convertibility is a SUBRELATION of it (the
fragment withdraws one rule), so the normalizer above soundly decides its YES direction.  The NO direction is the
shipped generator-count invariant (`ComputadWordProblem`: distinct generator counts ⟹ not `TwoCellConv`); what
remains is exactly the modulo-interchange overlap. -/

/-- ★ **Interchange-free convertibility implies FULL convertibility.**  Every interchange-free fragment step is a
genuine `TwoCellStep` (`twoCellStepInterchangeFree_isTwoCellStep`), hence a one-step `TwoCellConv`; the equivalence
closure transports through the `TwoCellConv` reflexivity / symmetry / transitivity constructors.  So deciding the
(convergent) interchange-free fragment is a SOUND decision of the YES direction of the full strict-2-category
2-cell equality the gate targets. -/
theorem interchangeFreeConv_imp_twoCellConv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (conv : Core.EquationalTheory (fun a b => TwoCellStepInterchangeFree signature a b) cellFirst cellSecond) :
    TwoCellConv signature cellFirst cellSecond := by
  induction conv with
  | rule step => exact TwoCellConv.ofStep (twoCellStepInterchangeFree_isTwoCellStep step)
  | refl point => exact TwoCellConv.refl point
  | symm _conv ih => exact TwoCellConv.symm ih
  | trans _first _second ihFirst ihSecond => exact TwoCellConv.trans ihFirst ihSecond

/-- ★ **Equal interchange-free normal forms imply FULL convertibility.**  Composes the convergent decision
(`interchangeFreeConv_iff_normalFormEq`) with the embedding into `TwoCellConv`.  This is the convergent
normalizer used as a SOUND positive semi-decision of the gate's `TwoCellConv`: where the normal forms coincide,
the cells are convertible in the full strict 2-category (interchange and all). -/
theorem normalFormEq_imp_twoCellConv (signature : ModeSignature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (normalFormsEqual :
      (interchangeFreeNormalizer signature sourcePath targetPath).normalize cellFirst =
        (interchangeFreeNormalizer signature sourcePath targetPath).normalize cellSecond) :
    TwoCellConv signature cellFirst cellSecond :=
  interchangeFreeConv_imp_twoCellConv
    ((interchangeFreeConv_iff_normalFormEq signature cellFirst cellSecond).mpr normalFormsEqual)

end FX1Poly.Tier0
