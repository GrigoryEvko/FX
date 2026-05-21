import LeanFX2.Reduction.ParStar
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Bridge
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.RawParWeakenInv.ParStar

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
