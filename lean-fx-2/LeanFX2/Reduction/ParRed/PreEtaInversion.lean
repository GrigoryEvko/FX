import LeanFX2.Bridge

/-! # LeanFX2.Reduction.ParRed.PreEtaInversion

Raw-projection inversion lemmas for binder-headed typed `Step.par`
sources.

These are deliberately weaker than roadmap T9/T10/T11.  The current
`Step.par` relation has no eta constructors, so the raw projection of a
parallel step out of `lam`, `lamPi`, or `pathLam` is still a matching
binder head.  The later eta-disjunctive typed destructors will extend
this pre-eta surface with the eta arm and typed reconstruction.
-/

namespace LeanFX2

namespace Step.par

/-- Raw-projection inversion for a non-dependent lambda source. -/
theorem lam_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep :
      Step.par
        (Term.lam (codomainType := codomainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.par bodyRawSource bodyRawTarget :=
  RawStep.par.lam_inv (Step.par.toRawBridge parallelStep)

/-- Raw-projection inversion for a dependent lambda source. -/
theorem lamPi_targetRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {targetType : Ty level scope} {targetRaw : RawTerm scope}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep :
      Step.par (Term.lamPi (domainType := domainType) bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.lam bodyRawTarget ∧
      RawStep.par bodyRawSource bodyRawTarget :=
  RawStep.par.lam_inv (Step.par.toRawBridge parallelStep)

/-- Raw-projection inversion for a path-lambda source. -/
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
    (parallelStep :
      Step.par
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        targetTerm) :
    ∃ bodyRawTarget,
      targetRaw = RawTerm.pathLam bodyRawTarget ∧
      RawStep.par bodyRawSource bodyRawTarget :=
  RawStep.par.pathLam_inv (Step.par.toRawBridge parallelStep)

end Step.par

end LeanFX2
