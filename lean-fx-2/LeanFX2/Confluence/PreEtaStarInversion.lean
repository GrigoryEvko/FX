import LeanFX2.Confluence.ParStarBridge
import LeanFX2.Confluence.RawParStarCong

/-! # LeanFX2.Confluence.PreEtaStarInversion

Raw-projection inversion lemmas for binder-headed typed `Step.parStar`
sources.

These are multi-step counterparts to
`Reduction/ParRed/PreEtaInversion.lean`.  They deliberately stay at the
raw projection layer: a typed chain starting from a binder-headed source
projects to a raw chain whose target keeps the same binder head, and the
body projection is related by `RawStep.parStar`.

This is still pre-eta infrastructure.  The later T9/T10/T11 typed
destructors need an additional eta disjunct plus typed reconstruction.
-/

namespace LeanFX2

namespace Step.parStar

/-- Raw-projection inversion for a multi-step chain from a non-dependent
lambda source. -/
theorem lam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain :
      Step.parStar
        (Term.lam (codomainType := codomainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  RawStep.parStar.lam_inv (Step.parStar.toRawBridge parallelChain)

/-- Raw-projection inversion for a multi-step chain from a dependent
lambda source. -/
theorem lamPi_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain :
      Step.parStar (Term.lamPi (domainType := domainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  RawStep.parStar.lam_inv (Step.parStar.toRawBridge parallelChain)

/-- Raw-projection inversion for a multi-step chain from a path-lambda
source. -/
theorem pathLam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain :
      Step.parStar
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.pathLam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  RawStep.parStar.pathLam_inv (Step.parStar.toRawBridge parallelChain)

end Step.parStar

namespace StepStar

/-- `StepStar` raw-projection inversion for a non-dependent lambda source.

This is the Conv-facing closure of
`Step.parStar.lam_targetRaw_inv_congr`: first lift the ordinary
single-step chain to a parallel chain, then reuse the raw binder-head
projection. -/
theorem lam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (chain :
      StepStar
        (Term.lam (codomainType := codomainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.lam_targetRaw_inv_congr chain.toParStar

/-- `StepStar` raw-projection inversion for a dependent lambda source. -/
theorem lamPi_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (chain :
      StepStar (Term.lamPi (domainType := domainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.lamPi_targetRaw_inv_congr chain.toParStar

/-- `StepStar` raw-projection inversion for a path-lambda source. -/
theorem pathLam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (chain :
      StepStar
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.pathLam bodyRawTarget ∧
      RawStep.parStar bodyRawSource bodyRawTarget :=
  Step.parStar.pathLam_targetRaw_inv_congr modeIsUnivalent carrierType
    leftEndpoint rightEndpoint chain.toParStar

end StepStar

end LeanFX2
