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

/-! ## Known-target raw-body pre-eta inversion

The current `Step.par` relation has no eta constructors.  These lemmas
are deliberately known-target destructors: once a caller has already
exposed the target as the same binder head, the raw projection reduces
to the corresponding raw body step.
-/

/-- Known-target raw-body inversion for non-dependent lambda parallel steps. -/
theorem lam_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons domainType) codomainType.weaken bodyRawSource}
    {bodyTarget :
      Term (context.cons domainType) codomainType.weaken bodyRawTarget}
    (parallelStep :
      Step.par
        (Term.lam (codomainType := codomainType) bodySource)
        (Term.lam (codomainType := codomainType) bodyTarget)) :
    RawStep.par bodyRawSource bodyRawTarget := by
  obtain ⟨bodyRawTarget', targetEq, bodyStep⟩ :=
    RawStep.par.lam_inv (Step.par.toRawBridge parallelStep)
  cases targetEq
  exact bodyStep

/-- Known-target raw-body inversion for dependent lambda parallel steps. -/
theorem lamPi_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource : Term (context.cons domainType) codomainType bodyRawSource}
    {bodyTarget : Term (context.cons domainType) codomainType bodyRawTarget}
    (parallelStep :
      Step.par (Term.lamPi (domainType := domainType) bodySource)
        (Term.lamPi (domainType := domainType) bodyTarget)) :
    RawStep.par bodyRawSource bodyRawTarget := by
  obtain ⟨bodyRawTarget', targetEq, bodyStep⟩ :=
    RawStep.par.lam_inv (Step.par.toRawBridge parallelStep)
  cases targetEq
  exact bodyStep

/-- Known-target raw-body inversion for path-lambda parallel steps. -/
theorem pathLam_bodyRaw_inv_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
    (parallelStep :
      Step.par
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodySource)
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyTarget)) :
    RawStep.par bodyRawSource bodyRawTarget := by
  obtain ⟨bodyRawTarget', targetEq, bodyStep⟩ :=
    RawStep.par.pathLam_inv (Step.par.toRawBridge parallelStep)
  cases targetEq
  exact bodyStep

end Step.par

end LeanFX2
