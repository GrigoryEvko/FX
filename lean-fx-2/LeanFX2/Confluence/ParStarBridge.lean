import LeanFX2.Reduction.ParStar
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Bridge
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.RawParWeakenInv.ParStar

/-! # ParStarBridge — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # Confluence/ParStarBridge — typed multi-step parallel chains
project to raw multi-step parallel chains, and the raw projections
of any two typed chains from a common source converge.

## Theorems shipped

* `Step.parStar.toRawBridge` — typed chain → raw chain.  Induction
  on the chain, applying `Step.par.toRawBridge` per step.
* `Step.parStar.toRawConfluence` — corollary: two typed chains
  from a common source produce raw projections that converge to
  a common raw reduct (via `RawStep.parStar.confluence`).

## Why this is the strongest typed confluence statement (for now)

Lifting the raw common reduct *back* to a typed Term whose
context+type matches both chain endpoints would require subject
reduction (preservation): given `Step.par t1 t2`, find a Ty for
the new raw target.  That theorem deserves its own phase
(planned Phase 7).  For Layers 4+ that consume confluence —
typed→raw projection + raw confluence is enough.

`Step.parStar.toRawConfluence` is what `Algo.DecConv` and the
elaborator's coherence proofs actually consume: "the two reducts
agree at the raw level" suffices for decidable conversion checks
because typed convertibility is preserved by typing
(elaboration-time invariant).
-/

namespace LeanFX2

/-- Typed multi-step parallel chain projects to a raw multi-step
parallel chain.  Induction on the chain: refl produces refl,
trans produces trans (single-step bridge + IH). -/
theorem Step.parStar.toRawBridge
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    RawStep.parStar sourceRaw targetRaw := by
  induction parallelChain with
  | refl _ => exact RawStep.parStar.refl _
  | trans firstStep _ restIH =>
      exact RawStep.parStar.trans
        (Step.par.toRawBridge firstStep) restIH

/-- Raw-projection compatibility of typed `parStar` under renaming.

This is the multi-step analogue of `Step.par.rename_toRawBridge`: it projects
the typed chain to raw, then uses raw `parStar` rename compatibility. -/
theorem Step.parStar.rename_toRawBridge
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    RawStep.parStar
      (Term.toRaw (Term.rename termRenaming sourceTerm))
      (Term.toRaw (Term.rename termRenaming targetTerm)) := by
  rw [Term.toRaw_rename termRenaming sourceTerm,
      Term.toRaw_rename termRenaming targetTerm]
  exact RawStep.parStar.rename_compatible rawRenaming
    (Step.parStar.toRawBridge parallelChain)

/-- `StepStar` variant of `Step.parStar.rename_toRawBridge`. -/
theorem StepStar.rename_toRawBridge
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    RawStep.parStar
      (Term.toRaw (Term.rename termRenaming sourceTerm))
      (Term.toRaw (Term.rename termRenaming targetTerm)) :=
  Step.parStar.rename_toRawBridge termRenaming chain.toParStar

/-- Canonical-weaken specialization of `Step.parStar.rename_toRawBridge`.

Multi-step analogue of `Step.par.weaken_toRawBridge`.  When a typed
`parStar` chain is weakened through one new binder via the canonical
`TermRenaming.weakenStep`, the raw projection of the weakened source
/ target is related by `RawStep.parStar`.  Surface form `Term.weaken
newType _` matches what D2.5 transp/hcomp cascades, K12.20 Kripke
chain construction, and Phase G β-η critical pair consumers reach
for at call sites. -/
theorem Step.parStar.weaken_toRawBridge
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    RawStep.parStar
      (Term.toRaw (Term.weaken newType sourceTerm))
      (Term.toRaw (Term.weaken newType targetTerm)) :=
  Step.parStar.rename_toRawBridge (TermRenaming.weakenStep context newType)
    parallelChain

/-- Canonical-weaken specialization of `StepStar.rename_toRawBridge`.

The `StepStar`-input shape consumers ordinarily reach for is the
narrow path: they ship a `StepStar` chain, ask the bridge for a raw
`parStar` chain at the weakened term.  This skips the manual
`chain.toParStar` + `weaken_toRawBridge` composition. -/
theorem StepStar.weaken_toRawBridge
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    RawStep.parStar
      (Term.toRaw (Term.weaken newType sourceTerm))
      (Term.toRaw (Term.weaken newType targetTerm)) :=
  StepStar.rename_toRawBridge (TermRenaming.weakenStep context newType) chain

/-- Raw-image compatibility for typed multi-step parallel reduction
after a typed substitution.

Multi-step analogue of `Step.par.subst_toRawBridge`: projects the typed
`parStar` chain to raw, then uses raw `parStar` subst-compatibility
lifted by `mapStep`. -/
theorem Step.parStar.subst_toRawBridge
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    RawStep.parStar (Term.toRaw (Term.subst termSubst sourceTerm))
                    (Term.toRaw (Term.subst termSubst targetTerm)) := by
  rw [Term.toRaw_subst termSubst sourceTerm,
      Term.toRaw_subst termSubst targetTerm]
  exact RawStep.parStar.subst_compatible_same sigma.forRaw
    (Step.parStar.toRawBridge parallelChain)

/-- Singleton-substitution specialization of `Step.parStar.subst_toRawBridge`.

The multi-step β-redex shape: `Term.subst0 body argTerm` for both
source and target of the typed `parStar` chain.  Surface form is what
K12.21 fundamental lemma multi-step β-arm and the Phase G β-η critical
pair joinability cascade reach for at call sites. -/
theorem Step.parStar.subst0_toRawBridge
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {substituent : Ty level scope}
    {argRaw : RawTerm scope}
    (argTerm : Term sourceCtx substituent argRaw)
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term (sourceCtx.cons substituent) sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons substituent) targetType targetRaw}
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    RawStep.parStar (Term.toRaw (Term.subst0 sourceTerm argTerm))
                    (Term.toRaw (Term.subst0 targetTerm argTerm)) :=
  Step.parStar.subst_toRawBridge (TermSubst.singleton argTerm) parallelChain

/-- `StepStar` variant of `Step.parStar.subst_toRawBridge`. -/
theorem StepStar.subst_toRawBridge
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    RawStep.parStar (Term.toRaw (Term.subst termSubst sourceTerm))
                    (Term.toRaw (Term.subst termSubst targetTerm)) :=
  Step.parStar.subst_toRawBridge termSubst chain.toParStar

/-- Singleton-substitution `StepStar` variant. -/
theorem StepStar.subst0_toRawBridge
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {substituent : Ty level scope}
    {argRaw : RawTerm scope}
    (argTerm : Term sourceCtx substituent argRaw)
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term (sourceCtx.cons substituent) sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons substituent) targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    RawStep.parStar (Term.toRaw (Term.subst0 sourceTerm argTerm))
                    (Term.toRaw (Term.subst0 targetTerm argTerm)) :=
  Step.parStar.subst0_toRawBridge argTerm chain.toParStar

/-- Typed-entrypoint raw image preservation for a renamed multi-step source.

If a typed `parStar` chain starts at `Term.rename termRenaming sourceTerm` and
the underlying raw renaming is injective, the target raw index remains in the
same raw renaming image.  This is still a raw/index theorem, not the full T5
payload with a reconstructed source-scope typed chain. -/
theorem Step.parStar.renamed_source_targetRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (parallelChain :
      Step.parStar (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      targetRaw = targetInnerRaw.rename rawRenaming :=
  RawStep.parStar.target_in_rename_image rawRenaming rawRenamingInjective
    (Step.parStar.toRawBridge parallelChain)

/-- Canonical-weaken specialization of
`Step.parStar.renamed_source_targetRaw_in_rename_image`. -/
theorem Step.parStar.weakened_source_targetRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (parallelChain :
      Step.parStar (Term.weaken newType sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      targetRaw = targetInnerRaw.weaken :=
  RawStep.parStar.target_in_weaken_image
    (Step.parStar.toRawBridge parallelChain)

/-- Typed `parStar` raw image preservation from a raw source equality.

This is the multi-step T5 source-equality shape at the typed entrypoint.  It
stays at raw/index level and therefore does not require subject reduction. -/
theorem Step.parStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      targetRaw = targetInnerRaw.rename rawRenaming :=
  RawStep.parStar.target_in_rename_image_of_source_eq rawRenaming
    rawRenamingInjective sourceEq
    (Step.parStar.toRawBridge parallelChain)

/-- Canonical-weaken specialization of
`Step.parStar.sourceRaw_in_rename_image_targetRaw_in_rename_image`. -/
theorem Step.parStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      targetRaw = targetInnerRaw.weaken :=
  RawStep.parStar.target_in_weaken_image_of_source_eq sourceEq
    (Step.parStar.toRawBridge parallelChain)

/-! ## Direct raw-chain packaging for rename-image parStar consumers -/

/-- Direct raw-chain packaging of
`Step.parStar.renamed_source_targetRaw_in_rename_image`.

If a typed `parStar` chain starts at a renamed typed term, its raw projection
can be targeted directly at a raw term in the same renaming image. -/
theorem Step.parStar.renamed_source_toRawBridge_target_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (parallelChain :
      Step.parStar (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      RawStep.parStar
        (Term.toRaw (Term.rename termRenaming sourceTerm))
        (targetInnerRaw.rename rawRenaming) := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.parStar.renamed_source_targetRaw_in_rename_image
      termRenaming rawRenamingInjective parallelChain
  cases targetEq
  exact ⟨targetInnerRaw, Step.parStar.toRawBridge parallelChain⟩

/-- Canonical-weaken specialization of
`Step.parStar.renamed_source_toRawBridge_target_in_rename_image`. -/
theorem Step.parStar.weakened_source_toRawBridge_target_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (parallelChain :
      Step.parStar (Term.weaken newType sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      RawStep.parStar
        (Term.toRaw (Term.weaken newType sourceTerm))
        targetInnerRaw.weaken := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.parStar.weakened_source_targetRaw_in_weaken_image
      newType parallelChain
  cases targetEq
  exact ⟨targetInnerRaw, Step.parStar.toRawBridge parallelChain⟩

/-- Direct raw-chain packaging of
`Step.parStar.sourceRaw_in_rename_image_targetRaw_in_rename_image`. -/
theorem Step.parStar.toRawBridge_target_in_rename_image_of_sourceRaw_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      RawStep.parStar sourceRaw (targetInnerRaw.rename rawRenaming) := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.parStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
      rawRenamingInjective sourceEq parallelChain
  cases targetEq
  exact ⟨targetInnerRaw, Step.parStar.toRawBridge parallelChain⟩

/-- Canonical-weaken specialization of
`Step.parStar.toRawBridge_target_in_rename_image_of_sourceRaw_eq`. -/
theorem Step.parStar.toRawBridge_target_in_weaken_image_of_sourceRaw_eq
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      RawStep.parStar sourceRaw targetInnerRaw.weaken := by
  obtain ⟨targetInnerRaw, targetEq⟩ :=
    Step.parStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
      sourceEq parallelChain
  cases targetEq
  exact ⟨targetInnerRaw, Step.parStar.toRawBridge parallelChain⟩

/-- `StepStar` variant of
`Step.parStar.renamed_source_targetRaw_in_rename_image`.

This is the ordinary multi-step reduction entrypoint used by `Conv`; it first
lifts the `StepStar` chain to `Step.parStar`, then applies the raw/index image
bridge above. -/
theorem StepStar.renamed_source_targetRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (chain : StepStar (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      targetRaw = targetInnerRaw.rename rawRenaming :=
  Step.parStar.renamed_source_targetRaw_in_rename_image
    termRenaming rawRenamingInjective chain.toParStar

/-- Canonical-weaken `StepStar` variant for ordinary multi-step consumers. -/
theorem StepStar.weakened_source_targetRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (chain : StepStar (Term.weaken newType sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      targetRaw = targetInnerRaw.weaken :=
  Step.parStar.weakened_source_targetRaw_in_weaken_image
    newType chain.toParStar

/-- `StepStar` raw image preservation from a raw source equality. -/
theorem StepStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (chain : StepStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      targetRaw = targetInnerRaw.rename rawRenaming :=
  Step.parStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
    rawRenamingInjective sourceEq chain.toParStar

/-- Canonical-weaken `StepStar` source-equality variant. -/
theorem StepStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (chain : StepStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      targetRaw = targetInnerRaw.weaken :=
  Step.parStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
    sourceEq chain.toParStar

/-- `StepStar` variant of
`Step.parStar.renamed_source_toRawBridge_target_in_rename_image`. -/
theorem StepStar.renamed_source_toRawBridge_target_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (chain : StepStar (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      RawStep.parStar
        (Term.toRaw (Term.rename termRenaming sourceTerm))
        (targetInnerRaw.rename rawRenaming) :=
  Step.parStar.renamed_source_toRawBridge_target_in_rename_image
    termRenaming rawRenamingInjective chain.toParStar

/-- Canonical-weaken `StepStar` variant of
`Step.parStar.weakened_source_toRawBridge_target_in_weaken_image`. -/
theorem StepStar.weakened_source_toRawBridge_target_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (chain : StepStar (Term.weaken newType sourceTerm) targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      RawStep.parStar
        (Term.toRaw (Term.weaken newType sourceTerm))
        targetInnerRaw.weaken :=
  Step.parStar.weakened_source_toRawBridge_target_in_weaken_image
    newType chain.toParStar

/-- `StepStar` variant of
`Step.parStar.toRawBridge_target_in_rename_image_of_sourceRaw_eq`. -/
theorem StepStar.toRawBridge_target_in_rename_image_of_sourceRaw_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (chain : StepStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm sourceScope,
      RawStep.parStar sourceRaw (targetInnerRaw.rename rawRenaming) :=
  Step.parStar.toRawBridge_target_in_rename_image_of_sourceRaw_eq
    rawRenamingInjective sourceEq chain.toParStar

/-- Canonical-weaken `StepStar` variant of
`Step.parStar.toRawBridge_target_in_weaken_image_of_sourceRaw_eq`. -/
theorem StepStar.toRawBridge_target_in_weaken_image_of_sourceRaw_eq
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (chain : StepStar sourceTerm targetTerm) :
    ∃ targetInnerRaw : RawTerm scope,
      RawStep.parStar sourceRaw targetInnerRaw.weaken :=
  Step.parStar.toRawBridge_target_in_weaken_image_of_sourceRaw_eq
    sourceEq chain.toParStar

/-- **Projection-confluence** for typed multi-step parallel
reduction.  Two typed chains from a common source produce raw
projections that converge to a common raw reduct.

Direct corollary of `Step.parStar.toRawBridge` +
`RawStep.parStar.confluence`.  The common raw reduct is `cd`
applied iteratively to the source's raw projection (constructively
the join point of the cd cascade).

Lifting this raw common reduct back to a typed Term requires
subject reduction (planned Phase 7); for now this is sufficient
for Layer 9 Algo's decidable-conversion needs. -/
theorem Step.parStar.toRawConfluence
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType leftType rightType : Ty level scope}
    {sourceRaw leftRaw rightRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {leftTarget : Term context leftType leftRaw}
    {rightTarget : Term context rightType rightRaw}
    (leftChain : Step.parStar sourceTerm leftTarget)
    (rightChain : Step.parStar sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw :=
  RawStep.parStar.confluence
    (Step.parStar.toRawBridge leftChain)
    (Step.parStar.toRawBridge rightChain)

end LeanFX2

-/
