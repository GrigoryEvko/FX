import LeanFX2.Reducibility.TypedCR2Generic

/-! # LeanFX2.Reducibility.TypedCR2Compound.IdentityLambda

K12.20.U4 identity-lambda SN-direct codomains.  Specialized
`fundamental_lam_*` lemmas where the lambda body reduces to a
type whose `Reducible` is plain SN.

## Root status

Layer 3 metatheory leaf.  First slice of the K12.20.U4 compound
cascade. -/

namespace LeanFX2




/-! ## K12.20.U4 identity lambda SN-direct codomains

These endpoints make the SN-codomain lambda route concrete for the
candidate arms where `Reducible` is definitionally recoverable from
strong normalization.  They remain identity-substitution endpoints for
the M04 path and deliberately do not claim the arbitrary compound
codomain case. -/

/-- Identity lambda reducibility for any codomain whose identity-
substituted candidate is SN-direct. -/
theorem Reducible.fundamental_identity_lam_at_arrow_SNDirect_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainTypeIsSNDirect :
      Reducible.IsSNDirect (codomainType.subst Subst.identity))
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := codomainType)
    (fun _resultTerm resultIsSN =>
      Reducible.of_isStronglyNormalizing_when_SNDirect
        codomainTypeIsSNDirect resultIsSN)
    bodyIH

/-- Identity lambda reducibility for a type-variable codomain.

`Ty.tyVar` is not an `IsSNDirect` arm because arbitrary substitution can
map it to any type.  Under identity substitution, the existing tyVar
SN-recovery lemma provides the same M04-facing lambda route. -/
theorem Reducible.fundamental_identity_lam_at_arrow_tyVar_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {position : Fin scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) (Ty.tyVar position).weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible ((Ty.tyVar position).weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType (Ty.tyVar position)).subst
      Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := Ty.tyVar position) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.tyVar position)
    (fun _resultTerm resultIsSN =>
      Reducible.tyVar_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Typed head-β SN expansion for dependent Π application.

`Term.lamPi` shares the raw `RawTerm.lam` constructor with non-dependent
lambda, and `Term.appPi` shares `RawTerm.app`.  Strong normalization is
raw-indexed, so the existing raw `app_lam` proof lifts directly to the
dependent application form. -/
theorem Term.appPi_lamPi_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {argumentRaw : RawTerm scope}
    {bodyTerm :
      Term (context.cons domainType) codomainType bodyRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm)
    (contractumIsSN :
      Term.isStronglyNormalizing (Term.subst0 bodyTerm argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.appPi (Term.lamPi bodyTerm) argumentTerm) :=
  RawTerm.app_lam_isStronglyNormalizing bodyIsSN argumentIsSN
    contractumIsSN

/-- Fundamental SN endpoint for `Term.lamPi` at `Ty.piTy`.

This is the dependent sibling of `fundamental_lam_at_arrow_sn`.  The
premise stays explicit: callers still need SN of the body under
`termSubst.lift domainType`. -/
theorem Reducible.fundamental_lamPi_at_piTy_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Term.subst (termSubst.lift domainType) bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.lamPi bodyTerm)) :=
  RawTerm.lam_isStronglyNormalizing bodyIsSN

/-- Renaming-stable SN of `Term.lamPi` at `Ty.piTy` —
`IsRenamingStableIsSN` mirror of `fundamental_lamPi_at_piTy_sn`.

The body lives under one additional binder, so at each renamed world
we extend `termRenaming` with `TermRenaming.lift (domainType.subst sigma)`
and the raw renaming with `rho.lift`.  `RawRenaming.lift_injective`
propagates injectivity into the binder world; the renamed body's raw
SN is then handed to `RawTerm.lam_isStronglyNormalizing` to rebuild
SN of the renamed `Term.lamPi` form. -/
theorem Reducible.fundamental_lamPi_at_piTy_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Term.subst (termSubst.lift domainType) bodyTerm)) :
    IsRenamingStableIsSN
      (Term.subst termSubst (Term.lamPi bodyTerm)) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have liftedInjective :=
    RawRenaming.lift_injective rho rhoIsInjective
  have liftedTermRenaming :=
    termRenaming.lift (domainType.subst sigma)
  have bodySNAtRho :=
    bodyIsStable liftedInjective liftedTermRenaming
  exact RawTerm.lam_isStronglyNormalizing bodySNAtRho

/-- Fundamental SN endpoint for the application closure of `Term.lamPi`.

The current `piTy` reducibility clause requires SN after dependent
application, not full reducibility at the substituted codomain.  This
lemma packages that exact M04-relevant obligation. -/
theorem Reducible.fundamental_lamPi_at_piTy_app_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Term.subst (termSubst.lift domainType) bodyTerm))
    (argumentReducible : Reducible (domainType.subst sigma) argumentTerm)
    (contractumIsSN :
      Term.isStronglyNormalizing
        (Term.subst0
          (Term.subst (termSubst.lift domainType) bodyTerm)
          argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.appPi
        (Term.subst termSubst (Term.lamPi bodyTerm))
        argumentTerm) :=
  Term.appPi_lamPi_isStronglyNormalizing bodyIsSN
    (Reducible.isStronglyNormalizing argumentReducible)
    contractumIsSN

/-- Renaming-stable head-β SN of `Term.appPi (Term.lamPi body) argument`
at `Ty.piTy` — `IsRenamingStableIsSN` mirror of
`fundamental_lamPi_at_piTy_app_sn`.

Same template as the non-dependent arrow variant: project the three
stable witnesses at each renamed world, align the contractum raw form
via `RawTerm.subst0_rename_commute`, then close with the raw head-β
combinator `RawTerm.app_lam_isStronglyNormalizing` — both `Term.app`
and `Term.appPi` share `RawTerm.app` raw, so the same combinator
closes the dependent variant. -/
theorem Reducible.fundamental_lamPi_at_piTy_app_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Term.subst (termSubst.lift domainType) bodyTerm))
    (argumentIsStable :
        IsRenamingStableReducible (domainType.subst sigma) argumentTerm)
    (contractumIsStable :
        IsRenamingStableIsSN
          (Term.subst0
            (Term.subst (termSubst.lift domainType) bodyTerm)
            argumentTerm)) :
    IsRenamingStableIsSN
      (Term.appPi
        (Term.subst termSubst (Term.lamPi bodyTerm))
        argumentTerm) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have liftedInjective :=
    RawRenaming.lift_injective rho rhoIsInjective
  have liftedTermRenaming :=
    termRenaming.lift (domainType.subst sigma)
  have bodySNAtRho :=
    bodyIsStable liftedInjective liftedTermRenaming
  have argumentReducibleAtRho :=
    argumentIsStable rhoIsInjective termRenaming
  have argumentSNAtRho :=
    Reducible.isStronglyNormalizing argumentReducibleAtRho
  have contractumSNAtRho :
      RawTerm.isStronglyNormalizing
        (((bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw).rename rho) :=
    contractumIsStable rhoIsInjective termRenaming
  rw [RawTerm.subst0_rename_commute] at contractumSNAtRho
  exact RawTerm.app_lam_isStronglyNormalizing bodySNAtRho
    argumentSNAtRho contractumSNAtRho

/-- β-contractum SN bridge for the `Term.lamPi` weak-Π case.

As in the non-dependent arrow bridge, the body IH naturally applies to
`TermSubst.consSingleton`, while the application endpoint wants the
`Term.subst0` contractum of the lifted body.  Since SN is raw-indexed,
the same raw substitution alignment closes the bridge. -/
theorem Reducible.fundamental_lamPi_at_piTy_contractum_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyContractumReducible :
      Reducible
        (codomainType.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst0
        (Term.subst (termSubst.lift domainType) bodyTerm)
        argumentTerm) := by
  have bodyContractumIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm) :=
    Reducible.isStronglyNormalizing bodyContractumReducible
  change RawTerm.isStronglyNormalizing
    ((bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw)
  rw [← RawTerm.subst_lift_singleton_eq_subst0
    bodyRaw domainType sigma argumentRaw]
  exact bodyContractumIsSN

/-- Renaming-stable β-contractum SN bridge for `Term.lamPi` at `Ty.piTy`
— `IsRenamingStableIsSN` mirror of `fundamental_lamPi_at_piTy_contractum_sn`.
Same pattern as the non-dependent lam_at_arrow contractum bridge: project
the consSingleton-form Reducible at each renamed world, demote to raw SN,
realign via `RawTerm.subst_lift_singleton_eq_subst0` lifted through
`rename rho`. -/
theorem Reducible.fundamental_lamPi_at_piTy_contractum_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyContractumIsStable :
      IsRenamingStableReducible
        (codomainType.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    IsRenamingStableIsSN
      (Term.subst0
        (Term.subst (termSubst.lift domainType) bodyTerm)
        argumentTerm) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have bodyContractumReducibleAtRho :=
    bodyContractumIsStable rhoIsInjective termRenaming
  have bodyContractumSNAtRho :
      RawTerm.isStronglyNormalizing
        ((bodyRaw.subst (Subst.compose sigma.lift
          (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw).rename
            rho) :=
    Reducible.isStronglyNormalizing bodyContractumReducibleAtRho
  show RawTerm.isStronglyNormalizing
    (((bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw).rename rho)
  rw [← RawTerm.subst_lift_singleton_eq_subst0
    bodyRaw domainType sigma argumentRaw]
  exact bodyContractumSNAtRho

/-- Combined SN endpoint for the `Term.lamPi` weak-Π application case. -/
theorem Reducible.fundamental_lamPi_at_piTy_app_sn_of_body_contractum
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Term.subst (termSubst.lift domainType) bodyTerm))
    (argumentReducible : Reducible (domainType.subst sigma) argumentTerm)
    (bodyContractumReducible :
      Reducible
        (codomainType.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.appPi
        (Term.subst termSubst (Term.lamPi bodyTerm))
        argumentTerm) :=
  Reducible.fundamental_lamPi_at_piTy_app_sn bodyIsSN argumentReducible
    (Reducible.fundamental_lamPi_at_piTy_contractum_sn
      bodyContractumReducible)

/-- Renaming-stable combined SN endpoint for `Term.lamPi` dependent
application — chains the three stable companions for the dependent-Π
head-β case. -/
theorem Reducible.fundamental_lamPi_at_piTy_app_sn_of_body_contractum_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Term.subst (termSubst.lift domainType) bodyTerm))
    (argumentIsStable :
        IsRenamingStableReducible (domainType.subst sigma) argumentTerm)
    (bodyContractumIsStable :
      IsRenamingStableReducible
        (codomainType.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    IsRenamingStableIsSN
      (Term.appPi
        (Term.subst termSubst (Term.lamPi bodyTerm))
        argumentTerm) :=
  Reducible.fundamental_lamPi_at_piTy_app_sn_stable bodyIsStable
    argumentIsStable
    (Reducible.fundamental_lamPi_at_piTy_contractum_sn_stable
      bodyContractumIsStable)

/-- Fundamental SN endpoint for `Term.pathLam` at cubical `Ty.path`.

This is the cubical sibling of `fundamental_lam_at_arrow_sn`.  The body
premise is explicit because generic lifted-substitution reducibility is
still the load-bearing `ReducibleSubst.lift` / weakening blocker. -/
theorem Reducible.fundamental_pathLam_at_path_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodyTerm)) :=
  Term.pathLam_isStronglyNormalizing modeIsUnivalent
    (carrierType.subst sigma)
    (leftEndpoint.subst sigma.forRaw)
    (rightEndpoint.subst sigma.forRaw)
    bodyIsSN

/-- Renaming-stable SN of `Term.pathLam` at `Ty.path` —
`IsRenamingStableIsSN` mirror of `fundamental_pathLam_at_path_sn`.

The cubical path binder sits over `Ty.interval`, which is closed,
so `Ty.interval.subst sigma = Ty.interval` reduces definitionally
and `termRenaming.lift Ty.interval` extends the renaming through
the interval-indexed binder.  `RawRenaming.lift_injective` carries
injectivity into the binder world; the raw renamed body SN then
feeds `RawTerm.pathLam_isStronglyNormalizing` via the typed wrapper. -/
theorem Reducible.fundamental_pathLam_at_path_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Ty.weaken_subst_commute sigma carrierType ▸
            Term.subst (termSubst.lift Ty.interval) bodyTerm)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodyTerm)) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have liftedInjective :=
    RawRenaming.lift_injective rho rhoIsInjective
  have liftedTermRenaming :=
    termRenaming.lift Ty.interval
  have bodySNAtRho :=
    bodyIsStable liftedInjective liftedTermRenaming
  exact RawTerm.pathLam_isStronglyNormalizing bodySNAtRho

/-- **K12.27 identity-substitution dependent lambda value SN endpoint**.

This is the `lamPi` sibling of
`fundamental_identity_lam_at_arrow_sn`.  It supplies the value-SN
conjunct needed by the identity-only M04 route without asserting the
substitution-parametric Π fundamental case. -/
theorem Reducible.fundamental_identity_lamPi_at_piTy_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (bodyIdentityReducible :
      Reducible (codomainType.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lamPi bodyTerm)) :=
  Reducible.fundamental_lamPi_at_piTy_sn
    (termSubst := TermSubst.identity sourceCtx)
    (Reducible.identity_lift_body_sn_of_identity_reducible_at
      bodyIdentityReducible)

/-- **K12.27 identity-substitution path lambda value SN endpoint**.

The cubical path binder has the same weakened-body shape as non-dependent
arrow lambda, with `Ty.interval` as the binder type.  This packages only
the identity-substitution value-SN endpoint for M04. -/
theorem Reducible.fundamental_identity_pathLam_at_path_sn
    {level scope : Nat}
    {sourceCtx : Ctx Mode.univalent level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyIdentityReducible :
      Reducible (carrierType.weaken.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons Ty.interval))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.pathLam rfl carrierType
          leftEndpoint rightEndpoint bodyTerm)) :=
  Reducible.fundamental_pathLam_at_path_sn
    (termSubst := TermSubst.identity sourceCtx)
    rfl
    (Reducible.identity_lift_body_sn_of_identity_reducible
      bodyIdentityReducible)

/-- Fundamental SN endpoint for cubical path-lambda application.

The path closure ultimately needs full `Reducible` at the carrier after
`pathApp`; this lemma packages only the M04-relevant SN half once the
lifted body, interval argument, and β-contractum are SN. -/
theorem Reducible.fundamental_pathLam_at_path_app_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalRaw : RawTerm targetScope}
    {intervalTerm : Term targetCtx Ty.interval intervalRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) bodyTerm))
    (intervalIsSN : Term.isStronglyNormalizing intervalTerm)
    (contractumIsSN :
      Term.isStronglyNormalizing
        (Term.subst0
          (Ty.weaken_subst_commute sigma carrierType ▸
            Term.subst (termSubst.lift Ty.interval) bodyTerm)
          intervalTerm)) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent
        (Term.subst termSubst
          (Term.pathLam modeIsUnivalent carrierType
            leftEndpoint rightEndpoint bodyTerm))
        intervalTerm) :=
  Term.pathApp_pathLam_isStronglyNormalizing modeIsUnivalent
    bodyIsSN intervalIsSN contractumIsSN

/-- Renaming-stable head-β SN of `Term.pathApp (Term.pathLam body) interval`
at `Ty.path` — `IsRenamingStableIsSN` mirror of
`fundamental_pathLam_at_path_app_sn`.

The interval binder is over closed `Ty.interval`, so the lifted
renaming uses `termRenaming.lift Ty.interval` directly.  Contractum
alignment reuses `RawTerm.subst0_rename_commute`; closure goes through
the raw cubical combinator `RawTerm.pathApp_pathLam_isStronglyNormalizing`
which K12.24.U5 already ships. -/
theorem Reducible.fundamental_pathLam_at_path_app_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalRaw : RawTerm targetScope}
    {intervalTerm : Term targetCtx Ty.interval intervalRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Ty.weaken_subst_commute sigma carrierType ▸
            Term.subst (termSubst.lift Ty.interval) bodyTerm))
    (intervalIsStable : IsRenamingStableIsSN intervalTerm)
    (contractumIsStable :
        IsRenamingStableIsSN
          (Term.subst0
            (Ty.weaken_subst_commute sigma carrierType ▸
              Term.subst (termSubst.lift Ty.interval) bodyTerm)
            intervalTerm)) :
    IsRenamingStableIsSN
      (Term.pathApp modeIsUnivalent
        (Term.subst termSubst
          (Term.pathLam modeIsUnivalent carrierType
            leftEndpoint rightEndpoint bodyTerm))
        intervalTerm) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have liftedInjective :=
    RawRenaming.lift_injective rho rhoIsInjective
  have liftedTermRenaming :=
    termRenaming.lift Ty.interval
  have bodySNAtRho :=
    bodyIsStable liftedInjective liftedTermRenaming
  have intervalSNAtRho :=
    intervalIsStable rhoIsInjective termRenaming
  have contractumSNAtRho :
      RawTerm.isStronglyNormalizing
        (((bodyRaw.subst sigma.forRaw.lift).subst0 intervalRaw).rename rho) :=
    contractumIsStable rhoIsInjective termRenaming
  rw [RawTerm.subst0_rename_commute] at contractumSNAtRho
  exact RawTerm.pathApp_pathLam_isStronglyNormalizing bodySNAtRho
    intervalSNAtRho contractumSNAtRho

/-- β-contractum SN bridge for cubical `Term.pathLam`.

The body IH is naturally available under `TermSubst.consSingleton` with
the interval argument.  As with arrow and Π, raw SN is insensitive to
the typed cast introduced by lifted substitution, so the raw
substitution-alignment lemma gives the target `Term.subst0` SN fact. -/
theorem Reducible.fundamental_pathLam_at_path_contractum_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalRaw : RawTerm targetScope}
    {intervalTerm : Term targetCtx Ty.interval intervalRaw}
    (bodyContractumReducible :
      Reducible
        (carrierType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (Ty.interval.subst sigma) intervalRaw)))
        (Term.subst
          (TermSubst.consSingleton (domainType := Ty.interval)
            termSubst intervalTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst0
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) bodyTerm)
        intervalTerm) := by
  have bodyContractumIsSN :
      Term.isStronglyNormalizing
        (Term.subst
          (TermSubst.consSingleton (domainType := Ty.interval)
            termSubst intervalTerm)
          bodyTerm) :=
    Reducible.isStronglyNormalizing bodyContractumReducible
  change RawTerm.isStronglyNormalizing
    ((bodyRaw.subst sigma.forRaw.lift).subst0 intervalRaw)
  rw [← RawTerm.subst_lift_singleton_eq_subst0
    bodyRaw Ty.interval sigma intervalRaw]
  exact bodyContractumIsSN

/-- Renaming-stable β-contractum SN bridge for cubical `Term.pathLam`
— `IsRenamingStableIsSN` mirror of `fundamental_pathLam_at_path_contractum_sn`.
Interval binder is closed (`Ty.interval`); same template as
`fundamental_lam_at_arrow_contractum_sn_stable`. -/
theorem Reducible.fundamental_pathLam_at_path_contractum_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalRaw : RawTerm targetScope}
    {intervalTerm : Term targetCtx Ty.interval intervalRaw}
    (bodyContractumIsStable :
      IsRenamingStableReducible
        (carrierType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (Ty.interval.subst sigma) intervalRaw)))
        (Term.subst
          (TermSubst.consSingleton (domainType := Ty.interval)
            termSubst intervalTerm)
          bodyTerm)) :
    IsRenamingStableIsSN
      (Term.subst0
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) bodyTerm)
        intervalTerm) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have bodyContractumReducibleAtRho :=
    bodyContractumIsStable rhoIsInjective termRenaming
  have bodyContractumSNAtRho :
      RawTerm.isStronglyNormalizing
        ((bodyRaw.subst (Subst.compose sigma.lift
          (Subst.singleton (Ty.interval.subst sigma) intervalRaw)).forRaw).rename
            rho) :=
    Reducible.isStronglyNormalizing bodyContractumReducibleAtRho
  show RawTerm.isStronglyNormalizing
    (((bodyRaw.subst sigma.forRaw.lift).subst0 intervalRaw).rename rho)
  rw [← RawTerm.subst_lift_singleton_eq_subst0
    bodyRaw Ty.interval sigma intervalRaw]
  exact bodyContractumSNAtRho

/-- Combined SN endpoint for cubical `Term.pathLam` application. -/
theorem Reducible.fundamental_pathLam_at_path_app_sn_of_body_contractum
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalRaw : RawTerm targetScope}
    {intervalTerm : Term targetCtx Ty.interval intervalRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma carrierType ▸
          Term.subst (termSubst.lift Ty.interval) bodyTerm))
    (intervalIsSN : Term.isStronglyNormalizing intervalTerm)
    (bodyContractumReducible :
      Reducible
        (carrierType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (Ty.interval.subst sigma) intervalRaw)))
        (Term.subst
          (TermSubst.consSingleton (domainType := Ty.interval)
            termSubst intervalTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent
        (Term.subst termSubst
          (Term.pathLam modeIsUnivalent carrierType
            leftEndpoint rightEndpoint bodyTerm))
        intervalTerm) :=
  Reducible.fundamental_pathLam_at_path_app_sn modeIsUnivalent
    bodyIsSN intervalIsSN
    (Reducible.fundamental_pathLam_at_path_contractum_sn
      bodyContractumReducible)

/-- Renaming-stable combined SN endpoint for cubical `Term.pathLam`
application — chains the three stable companions for the cubical
head-β case. -/
theorem Reducible.fundamental_pathLam_at_path_app_sn_of_body_contractum_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalRaw : RawTerm targetScope}
    {intervalTerm : Term targetCtx Ty.interval intervalRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Ty.weaken_subst_commute sigma carrierType ▸
            Term.subst (termSubst.lift Ty.interval) bodyTerm))
    (intervalIsStable : IsRenamingStableIsSN intervalTerm)
    (bodyContractumIsStable :
      IsRenamingStableReducible
        (carrierType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (Ty.interval.subst sigma) intervalRaw)))
        (Term.subst
          (TermSubst.consSingleton (domainType := Ty.interval)
            termSubst intervalTerm)
          bodyTerm)) :
    IsRenamingStableIsSN
      (Term.pathApp modeIsUnivalent
        (Term.subst termSubst
          (Term.pathLam modeIsUnivalent carrierType
            leftEndpoint rightEndpoint bodyTerm))
        intervalTerm) :=
  Reducible.fundamental_pathLam_at_path_app_sn_stable modeIsUnivalent
    bodyIsStable intervalIsStable
    (Reducible.fundamental_pathLam_at_path_contractum_sn_stable
      bodyContractumIsStable)


end LeanFX2
