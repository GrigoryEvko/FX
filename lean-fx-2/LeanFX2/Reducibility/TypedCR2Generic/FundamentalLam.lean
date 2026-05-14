import LeanFX2.Reducibility.TypedCR2Generic.SubstLift

/-! # LeanFX2.Reducibility.TypedCR2Generic.FundamentalLam

`Term.lam` at `Ty.arrow` fundamental closure — the Wood/Atkey
2022 corrected lambda case.  Includes the cons-singleton
`ReducibleSubst` extension, β-contractum bridges, body-IH
forms, and the SN-recoverable codomain variants used when the
codomain admits only SN closure rather than full Reducible.

## Root status

Layer 3 metatheory leaf.  Fifth slice of `TypedCR2Generic`. -/

namespace LeanFX2

/-- **K12.27 identity-substitution lambda value SN endpoint**.

This composes the identity-lift body bridge with the existing lambda
SN endpoint.  It is the identity-only counterpart of
`fundamental_lam_at_arrow_sn`: the body premise is the body IH under
`TermSubst.identity` in the extended context, not a generic lifted
substitution reducibility theorem. -/
theorem Reducible.fundamental_identity_lam_at_arrow_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyIdentityReducible :
      Reducible (codomainType.weaken.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Reducible.fundamental_lam_at_arrow_sn
    (termSubst := TermSubst.identity sourceCtx)
    (Reducible.identity_lift_body_sn_of_identity_reducible
      bodyIdentityReducible)

/-- **K12.20.U3 cons-singleton ReducibleSubst**: extending an existing
reducible substitution with a reducible β argument yields a reducible
substitution for the extended source context into the original target
context.

This is intentionally weaker and more specific than
`ReducibleSubst.lift`.  It is the substitution shape needed by the
lambda-body β contractum and does not require arbitrary
world-monotone weakening of old reducibility witnesses. -/
theorem ReducibleSubst.consSingleton
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substReducible : ReducibleSubst termSubst)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (argumentReducible : Reducible (domainType.subst sigma) argumentTerm) :
    ReducibleSubst
      (TermSubst.consSingleton termSubst argumentTerm) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          change Reducible
            (domainType.weaken.subst
              (Subst.compose sigma.lift
                (Subst.singleton (domainType.subst sigma) argumentRaw)))
            ((Ty.weaken_subst_lift_singleton domainType domainType sigma
              argumentRaw).symm ▸ argumentTerm)
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_lift_singleton domainType domainType sigma
              argumentRaw)
            argumentReducible
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
          have typeEq :
              ((varType (sourceCtx.cons domainType)
                  ⟨previousIndex + 1, positionIsWithinScope⟩).subst
                (Subst.compose sigma.lift
                  (Subst.singleton (domainType.subst sigma) argumentRaw))) =
                (varType sourceCtx previousPosition).subst sigma := by
            exact Ty.weaken_subst_lift_singleton
              (varType sourceCtx previousPosition) domainType sigma argumentRaw
          have rawEq :
              (Subst.compose sigma.lift
                  (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw
                  ⟨previousIndex + 1, positionIsWithinScope⟩ =
                sigma.forRaw previousPosition := by
            exact RawTerm.weaken_subst_singleton
              (sigma.forRaw previousPosition) argumentRaw
          change Reducible
            ((varType (sourceCtx.cons domainType)
                ⟨previousIndex + 1, positionIsWithinScope⟩).subst
              (Subst.compose sigma.lift
                (Subst.singleton (domainType.subst sigma) argumentRaw)))
            (rawEq.symm ▸ typeEq.symm ▸ termSubst previousPosition)
          exact Reducible.of_raw_eq_symm_cast rawEq
            (Reducible.of_type_eq_symm_cast typeEq
              (substReducible previousPosition))

/-- Full β-contractum reducibility bridge for the `Term.lam` arrow case,
assuming the typed substitution-composition HEq.

The body IH produces reducibility for `Term.subst` under
`TermSubst.consSingleton`.  The arrow application closure needs
reducibility of the concrete `Term.subst0` contractum produced from the
substituted lambda body.  Raw and type indices already align by the
β-specific substitution laws; the remaining non-definitional content is
the supplied Term-level HEq. -/
theorem Reducible.fundamental_lam_at_arrow_contractum
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (contractumHEq :
      HEq
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)
        (Term.subst0
          (Ty.weaken_subst_commute sigma codomainType ▸
            Term.subst (termSubst.lift domainType) bodyTerm)
          argumentTerm))
    (bodyContractumReducible :
      Reducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Reducible
      ((codomainType.subst sigma).weaken.subst0
        (domainType.subst sigma) argumentRaw)
      (Term.subst0
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm)
        argumentTerm) := by
  have typeEq :
      codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)) =
        (codomainType.subst sigma).weaken.subst0
          (domainType.subst sigma) argumentRaw := by
    exact (Ty.weaken_subst_lift_singleton codomainType domainType sigma
      argumentRaw).trans
        (Ty.weaken_subst_singleton (codomainType.subst sigma)
          (domainType.subst sigma) argumentRaw).symm
  have rawEq :
      bodyRaw.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw =
        (bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw :=
    RawTerm.subst_lift_singleton_eq_subst0
      bodyRaw domainType sigma argumentRaw
  exact Reducible.of_heq typeEq rawEq contractumHEq
    bodyContractumReducible

/-- Lambda reducibility from the body IH under `consSingleton`, once the
typed β-contractum HEq is available.

This is the directly usable form of
`fundamental_lam_at_arrow_of_sn_codomain` for the Wood/Atkey lambda
case.  It keeps the two remaining obligations explicit:

* the lifted body is reducible at the weakened substituted codomain;
* each body contractum under `TermSubst.consSingleton` is HEq to the
  concrete `Term.subst0` target.

The body IH plus `ReducibleSubst.consSingleton` supplies
`bodyContractumReducible`; the missing cast-aware substitution theorem
supplies `bodyContractumHEq`. -/
theorem Reducible.fundamental_lam_at_arrow_of_consSingleton
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (bodyLiftReducible :
      Reducible ((codomainType.subst sigma).weaken)
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm))
    (bodyContractumHEq :
      ∀ {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw),
        HEq
          (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
            bodyTerm)
          (Term.subst0
            (Ty.weaken_subst_commute sigma codomainType ▸
              Term.subst (termSubst.lift domainType) bodyTerm)
            argumentTerm))
    (bodyContractumReducible :
      ∀ {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw),
        Reducible (domainType.subst sigma) argumentTerm →
        Reducible
          (codomainType.weaken.subst
            (Subst.compose sigma.lift
              (Subst.singleton (domainType.subst sigma) argumentRaw)))
          (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
            bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Reducible.fundamental_lam_at_arrow_of_sn_codomain
    codomainReducibleOfSN
    bodyLiftReducible
    (fun argumentTerm argumentReducible =>
      Reducible.fundamental_lam_at_arrow_contractum
        (bodyContractumHEq argumentTerm)
        (bodyContractumReducible argumentTerm argumentReducible))

/-- Lambda reducibility from the substitution-parametric body IH, modulo
the two remaining infrastructure blockers.

This theorem packages the Wood/Atkey lambda case up to:

* `liftSubstReducible`, the generic `ReducibleSubst.lift` obligation;
* `bodyContractumHEq`, the cast-aware β contractum substitution HEq;
* `codomainReducibleOfSN`, needed only for codomains whose candidate is
  recovered from SN at this frontier.

The body contractum side is no longer a blocker here: it is obtained by
calling the body IH under `TermSubst.consSingleton`, whose reducibility
is already supplied by `ReducibleSubst.consSingleton`. -/
theorem Reducible.fundamental_lam_at_arrow_of_bodyIH
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (substReducible : ReducibleSubst termSubst)
    (liftSubstReducible : ReducibleSubst (termSubst.lift domainType))
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm))
    (bodyContractumHEq :
      ∀ {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw),
        HEq
          (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
            bodyTerm)
          (Term.subst0
            (Ty.weaken_subst_commute sigma codomainType ▸
              Term.subst (termSubst.lift domainType) bodyTerm)
            argumentTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  have bodyLiftReducible :
      Reducible ((codomainType.subst sigma).weaken)
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm) :=
    Reducible.of_type_eq_cast
      (Ty.weaken_subst_commute sigma codomainType)
      (bodyIH (termSubst.lift domainType) liftSubstReducible)
  exact Reducible.fundamental_lam_at_arrow_of_consSingleton
    codomainReducibleOfSN
    bodyLiftReducible
    bodyContractumHEq
    (fun argumentTerm argumentReducible =>
      bodyIH (TermSubst.consSingleton termSubst argumentTerm)
        (ReducibleSubst.consSingleton substReducible argumentReducible))

/-- β-contractum SN bridge for the `Term.lam` arrow case.

The body IH naturally applies to `TermSubst.consSingleton`, whose raw
substitution is `sigma.lift` composed with a singleton argument
substitution.  The application SN endpoint wants the equivalent
`Term.subst0` contractum of the lifted body.  This lemma is exactly
that raw-alignment bridge, demoted to the SN endpoint needed by M04. -/
theorem Reducible.fundamental_lam_at_arrow_contractum_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyContractumReducible :
      Reducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst0
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm)
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

/-- Renaming-stable β-contractum SN bridge for `Term.lam` at `Ty.arrow`
— `IsRenamingStableIsSN` mirror of `fundamental_lam_at_arrow_contractum_sn`.

At each renamed world, project the stable consSingleton-form Reducible
witness, demote to raw SN, and align the raw form via
`RawTerm.subst_lift_singleton_eq_subst0` (which expresses the
consSingleton substitution as a lift-then-subst0 composition).  Rename
factors through both sides, so the bridge composes through `rename`. -/
theorem Reducible.fundamental_lam_at_arrow_contractum_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyContractumIsStable :
      IsRenamingStableReducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    IsRenamingStableIsSN
      (Term.subst0
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm)
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

/-- Combined SN endpoint for the `Term.lam` arrow application case.

This composes the three lambda SN pieces shipped so far:

* SN of the lifted body gives SN of the substituted lambda value.
* Reducibility of the argument gives SN of the argument.
* Reducibility of the body under `TermSubst.consSingleton` gives SN of
  the β-contractum aligned with `Term.subst0`.

The result is intentionally only the SN half of the arrow application
closure.  Full codomain `Reducible` still needs the separate
head-β/full-reducibility transport across the lifted-body cast. -/
theorem Reducible.fundamental_lam_at_arrow_app_sn_of_body_contractum
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm))
    (argumentReducible : Reducible (domainType.subst sigma) argumentTerm)
    (bodyContractumReducible :
      Reducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.app
        (Term.subst termSubst
          (Term.lam (codomainType := codomainType) bodyTerm))
        argumentTerm) :=
  Reducible.fundamental_lam_at_arrow_app_sn bodyIsSN argumentReducible
    (Reducible.fundamental_lam_at_arrow_contractum_sn
      bodyContractumReducible)

/-- Renaming-stable combined SN endpoint for `Term.lam` arrow application
— composes the three `_stable` companions (body / argument / contractum)
into the renaming-stable head-β SN endpoint.

This is the `IsRenamingStableIsSN` counterpart to
`fundamental_lam_at_arrow_app_sn_of_body_contractum`; the proof is a
direct corollary of `fundamental_lam_at_arrow_app_sn_stable` (which
takes head-β SN as a stable contractum SN) composed with
`fundamental_lam_at_arrow_contractum_sn_stable` (which produces that
stable contractum SN from the consSingleton-form body IH). -/
theorem Reducible.fundamental_lam_at_arrow_app_sn_of_body_contractum_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Ty.weaken_subst_commute sigma codomainType ▸
            Term.subst (termSubst.lift domainType) bodyTerm))
    (argumentIsStable :
        IsRenamingStableReducible (domainType.subst sigma) argumentTerm)
    (bodyContractumIsStable :
      IsRenamingStableReducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    IsRenamingStableIsSN
      (Term.app
        (Term.subst termSubst
          (Term.lam (codomainType := codomainType) bodyTerm))
        argumentTerm) :=
  Reducible.fundamental_lam_at_arrow_app_sn_stable bodyIsStable
    argumentIsStable
    (Reducible.fundamental_lam_at_arrow_contractum_sn_stable
      bodyContractumIsStable)

/-- Lambda reducibility from the body IH for SN-recoverable codomains,
without the typed β-contractum HEq.

For codomains whose reducibility candidate can be rebuilt from strong
normalization, the arrow application closure only needs SN of the
β-redex.  That SN fact is already supplied by the raw-indexed
`fundamental_lam_at_arrow_app_sn_of_body_contractum` bridge from the
body IH under `TermSubst.consSingleton`; no typed contractum HEq is
needed on this narrower route. -/
theorem Reducible.fundamental_lam_at_arrow_of_bodyIH_sn_codomain
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (substReducible : ReducibleSubst termSubst)
    (liftSubstReducible : ReducibleSubst (termSubst.lift domainType))
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  have bodyLiftReducible :
      Reducible ((codomainType.subst sigma).weaken)
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm) :=
    Reducible.of_type_eq_cast
      (Ty.weaken_subst_commute sigma codomainType)
      (bodyIH (termSubst.lift domainType) liftSubstReducible)
  have bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm) :=
    Reducible.isStronglyNormalizing bodyLiftReducible
  refine ⟨
    Reducible.fundamental_lam_at_arrow_sn
      (termSubst := termSubst)
      bodyIsSN,
    ?_⟩
  intro _argumentRaw argumentTerm argumentReducible
  exact codomainReducibleOfSN
    (Term.app
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm))
      argumentTerm)
    (Reducible.fundamental_lam_at_arrow_app_sn_of_body_contractum
      (termSubst := termSubst)
      bodyIsSN
      argumentReducible
      (bodyIH
        (TermSubst.consSingleton termSubst argumentTerm)
        (ReducibleSubst.consSingleton substReducible argumentReducible)))

/-- Lambda reducibility from a renaming-stable substitution and the body
IH, for SN-recoverable codomains.

This removes the explicit `liftSubstReducible` frontier premise from
`fundamental_lam_at_arrow_of_bodyIH_sn_codomain`: the lifted
substitution is now built by `ReducibleSubst.lift_of_renamingStable`.
The theorem is still honest about its scope: it only covers codomains
whose reducibility can be recovered from SN, and the full
substituted-codomain contractum reducibility route still needs the
typed β-contractum HEq. -/
theorem Reducible.fundamental_lam_at_arrow_of_stable_bodyIH_sn_codomain
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (substReducible : ReducibleSubst termSubst)
    (substIsStable : IsRenamingStableReducibleSubst termSubst)
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Reducible.fundamental_lam_at_arrow_of_bodyIH_sn_codomain
    codomainReducibleOfSN
    substReducible
    (ReducibleSubst.lift_of_renamingStable substIsStable domainType)
    bodyIH

/-- Identity-substitution lambda reducibility for SN-recoverable codomains.

This is the M04-facing specialization of
`fundamental_lam_at_arrow_of_bodyIH_sn_codomain`.  The value-SN side uses
the existing identity-lift bridge instead of generic
`ReducibleSubst.lift`; the application side still uses the body IH under
`TermSubst.consSingleton`, so reducible arguments feed the β-contractum
without requiring the typed β-contractum HEq. -/
theorem Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm scope}
        (resultTerm :
          Term sourceCtx (codomainType.subst Subst.identity) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst Subst.identity) resultTerm)
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
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  have bodyIdentityReducible :
      Reducible (codomainType.weaken.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm) :=
    bodyIH (TermSubst.identity (sourceCtx.cons domainType))
      ReducibleSubst.identity
  have bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute Subst.identity codomainType ▸
          Term.subst ((TermSubst.identity sourceCtx).lift domainType)
            bodyTerm) :=
    Reducible.identity_lift_body_sn_of_identity_reducible
      bodyIdentityReducible
  refine ⟨
    Reducible.fundamental_lam_at_arrow_sn
      (termSubst := TermSubst.identity sourceCtx)
      bodyIsSN,
    ?_⟩
  intro _argumentRaw argumentTerm argumentReducible
  exact codomainReducibleOfSN
    (Term.app
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := codomainType) bodyTerm))
      argumentTerm)
    (Reducible.fundamental_lam_at_arrow_app_sn_of_body_contractum
      (termSubst := TermSubst.identity sourceCtx)
      bodyIsSN
      argumentReducible
      (bodyIH
        (TermSubst.consSingleton
          (TermSubst.identity sourceCtx) argumentTerm)
        (ReducibleSubst.consSingleton
          ReducibleSubst.identity argumentReducible)))



end LeanFX2
