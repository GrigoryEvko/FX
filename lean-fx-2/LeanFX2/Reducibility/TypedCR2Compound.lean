import LeanFX2.Reducibility.TypedCR2Generic

/-! # LeanFX2.Reducibility.TypedCR2Compound — K12.20.U4 identity λ + F-T

Typed forward-step closure for compound Reducible arms (the
"specialized closure" arms that go beyond plain SN).

## What ships

* K12.20.U4 identity lambda SN-direct codomains — variant lemmas
  for `Term.lam` at codomain types that are SN-direct.  This is
  the foundation for the fundamental_lam case (Wood/Atkey 2022
  Lam rule, #1928).
* K12.20.F — typed CR2 lift for `Ty.arrow` (proper closure: maps
  Reducible to Reducible).
* K12.20.G — typed CR2 lift for `Ty.piTy` (SN-output compound).
* K12.20.H — typed CR2 lift for `Ty.sigmaTy` (asymmetric closure).
* K12.20.I — typed CR2 lift for `Ty.id` (SN-output idJ).
* K12.20.J — typed CR2 lift for `Ty.listType` (SN-output elim).
* K12.20.K — typed CR2 lift for `Ty.optionType` (weak elim).
* K12.20.L — typed CR2 lift for `Ty.eitherType` (symmetric SN
  elim).
* K12.20.M — typed CR2 lift for `Ty.path` (strong pathApp).
* K12.20.N — typed CR2 lift for `Ty.glue` (strong glueElim).
* K12.20.O — typed CR2 lift for `Ty.oeq` (SN-output oeqJ).
* K12.20.P — typed CR2 lift for `Ty.idStrict` (weak idStrictRec).
* K12.20.Q — typed CR2 lift for `Ty.equiv` (strong equivApp).
* K12.20.R — typed CR2 lift for `Ty.refine` (strong refineElim).
* K12.20.S — typed CR2 lift for `Ty.record` (strong recordProj).
* K12.20.T — typed CR2 lift for `Ty.codata` (strong codataDest).

## Root status

Layer 3 metatheory leaf.  Consumed by `TypedCR2Wrapup`
(unified Reducible.step_preserves). -/

namespace LeanFX2


/-! ## K12.20.U4 identity lambda SN-direct codomains

These endpoints make the SN-codomain lambda route concrete for the
candidate arms where `Reducible` is definitionally recoverable from
strong normalization.  They remain identity-substitution endpoints for
the M04 path and deliberately do not claim the arbitrary compound
codomain case. -/

/-- Identity lambda reducibility for a unit codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_unit_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (sourceCtx.cons domainType) Ty.unit.weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (Ty.unit.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType Ty.unit).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := Ty.unit) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.unit)
    (fun _resultTerm resultIsSN =>
      Reducible.unit_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for a boolean codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_bool_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (sourceCtx.cons domainType) Ty.bool.weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (Ty.bool.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType Ty.bool).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := Ty.bool) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.bool)
    (fun _resultTerm resultIsSN =>
      Reducible.bool_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for a natural-number codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_nat_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (sourceCtx.cons domainType) Ty.nat.weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (Ty.nat.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType Ty.nat).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := Ty.nat) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.nat)
    (fun _resultTerm resultIsSN =>
      Reducible.nat_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for an empty-type codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_empty_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (sourceCtx.cons domainType) Ty.empty.weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (Ty.empty.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType Ty.empty).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := Ty.empty) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.empty)
    (fun _resultTerm resultIsSN =>
      Reducible.empty_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for an interval codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_interval_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (sourceCtx.cons domainType) Ty.interval.weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (Ty.interval.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType Ty.interval).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := Ty.interval) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.interval)
    (fun _resultTerm resultIsSN =>
      Reducible.interval_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for a universe-code codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_universe_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType)
        (Ty.universe universeLevel levelLe).weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible ((Ty.universe universeLevel levelLe).weaken.subst
          bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible
      ((Ty.arrow domainType
        (Ty.universe universeLevel levelLe)).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam
          (codomainType := Ty.universe universeLevel levelLe) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.universe universeLevel levelLe)
    (fun _resultTerm resultIsSN =>
      Reducible.universe_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for a type-variable codomain. -/
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

/-- Identity lambda reducibility for a session codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_session_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {protocolStep : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType)
        (Ty.session protocolStep).weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible ((Ty.session protocolStep).weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType (Ty.session protocolStep)).subst
      Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := Ty.session protocolStep) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.session protocolStep)
    (fun _resultTerm resultIsSN =>
      Reducible.session_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for an effect codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_effect_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType)
        (Ty.effect carrierType effectTag).weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible ((Ty.effect carrierType effectTag).weaken.subst
          bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible
      ((Ty.arrow domainType
        (Ty.effect carrierType effectTag)).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam
          (codomainType := Ty.effect carrierType effectTag) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.effect carrierType effectTag)
    (fun _resultTerm resultIsSN =>
      Reducible.effect_of_isStronglyNormalizing resultIsSN)
    bodyIH

/-- Identity lambda reducibility for a modal codomain. -/
theorem Reducible.fundamental_identity_lam_at_arrow_modal_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType carrierType : Ty level scope}
    {modalityTag : Nat}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType)
        (Ty.modal modalityTag carrierType).weaken bodyRaw}
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible ((Ty.modal modalityTag carrierType).weaken.subst
          bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible
      ((Ty.arrow domainType
        (Ty.modal modalityTag carrierType)).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam
          (codomainType := Ty.modal modalityTag carrierType) bodyTerm)) :=
  Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    (codomainType := Ty.modal modalityTag carrierType)
    (fun _resultTerm resultIsSN =>
      Reducible.modal_of_isStronglyNormalizing resultIsSN)
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

/-! ## K12.20.F typed CR2 lift for compound Reducible arms — Ty.arrow

The first of 15 compound-arm CR2 lemmas.  Unlike the 10 SN-direct
arms (K12.20.D), compound arms have closure structure beyond pure SN
that must also be preserved under reduction.

For `Ty.arrow A B`, `Reducible` says: SN(f) ∧ (∀ arg, Reducible A arg
→ Reducible B (app f arg)).  Preserving this under f → f' requires:
1. SN(f'), via K12.20.B's raw `step_preserves` on the SN conjunct.
2. ∀ arg, Reducible A arg → Reducible B (app f' arg).  Given
   `Reducible B (app f arg)` (from source's closure), and step
   `app f arg → app f' arg` (via RawStep.par.app + refl on arg),
   the new closure conclusion follows from CR2 at codomain — the
   recursive ingredient supplied as `codomainCR2`.

Per the warrior-mentality discipline of CLAUDE.md, K12.20.F ships
the arrow case taking `codomainCR2` as an explicit hypothesis rather
than wiring up structural recursion on Ty here.  This keeps the
proof atomic and one-shot.  K12.20.G+ ship the remaining 14
compound arms, each with the same shape (recursion-hypothesis
taken as argument).  The final combined `Reducible.step_preserves`
will be a structurally-recursive bundle wiring all 25 arms together;
its body will invoke each per-arm helper at the right recursive
position.
-/

/-- **K12.20.F arrow arm**: Reducible at `Ty.arrow domain codomain`
is preserved under raw `parProgress` reduction.  Body: SN preserved
via K12.20.B, closure preserved via codomainCR2 + raw app-cong. -/
theorem Reducible.step_preserves_arrow
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.arrow domainType codomainType) sourceRaw}
    {target : Term context (Ty.arrow domainType codomainType) targetRaw}
    (sourceReducible : Reducible (Ty.arrow domainType codomainType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw)
    (codomainCR2 :
        ∀ {sourceRaw' targetRaw' : RawTerm scope}
          {source' : Term context codomainType sourceRaw'}
          {target' : Term context codomainType targetRaw'},
          Reducible codomainType source' →
          RawStep.parProgress sourceRaw' targetRaw' →
          Reducible codomainType target') :
    Reducible (Ty.arrow domainType codomainType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argRaw argTerm argReducible
    have appStep : RawStep.parProgress
        (RawTerm.app sourceRaw argRaw) (RawTerm.app targetRaw argRaw) := by
      refine ⟨RawStep.par.app rawStep.1 (RawStep.par.refl argRaw), ?_⟩
      intro appEq
      apply rawStep.2
      injection appEq
    exact codomainCR2 (sourceReducible.2 argTerm argReducible) appStep

/-! ## K12.20.G typed CR2 lift — Ty.piTy SN-output compound arm

Second compound-arm CR2 lemma.  `Ty.piTy` ships an **SN-output
closure** in K12.6:

```
Reducible (Ty.piTy A B) f =
  SN(f) ∧ ∀ arg, Reducible A arg → SN(Term.appPi f arg)
```

The eliminator output is `SN(appPi f arg)` not `Reducible
codomain (appPi f arg)`.  Consequently, CR2 for piTy needs NO
recursive codomainCR2 hypothesis — both SN preservation (the SN
conjunct) and the eliminator-output closure are pure-SN
preservation, both discharged by K12.20.B's raw `step_preserves`.
This is the simplest compound-arm CR2 of the 15.

Term.appPi's raw projection IS `RawTerm.app` (per Term.lean:127,
`Term.appPi : Term ctx (cod.subst0 dom arg) (RawTerm.app f a)`),
not a separate `RawTerm.appPi`.  So the same `RawStep.par.app`
cong rule we used in K12.20.F applies here.
-/

/-- **K12.20.G piTy arm**: weak-closure CR2 for `Ty.piTy`.  Both
SN-of-functionTerm and SN-of-appPi-result are preserved by the same
raw `step_preserves`.  Distinctness on app via ctor injectivity, same
as K12.20.F. -/
theorem Reducible.step_preserves_piTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.piTy domainType codomainType) sourceRaw}
    {target : Term context (Ty.piTy domainType codomainType) targetRaw}
    (sourceReducible :
        Reducible (Ty.piTy domainType codomainType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.piTy domainType codomainType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argRaw argTerm argReducible
    have appStep : RawStep.parProgress
        (RawTerm.app sourceRaw argRaw) (RawTerm.app targetRaw argRaw) := by
      refine ⟨RawStep.par.app rawStep.1 (RawStep.par.refl argRaw), ?_⟩
      intro appEq
      apply rawStep.2
      injection appEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 argTerm argReducible) appStep

/-! ## K12.20.H typed CR2 lift — Ty.sigmaTy asymmetric-closure compound arm

Third compound-arm CR2 lemma.  `Ty.sigmaTy` ships an **asymmetric
closure** in K12.7 (the second conjunct is full Reducible on the
fst projection because `firstType` IS a strict sub-Ty of
`Ty.sigmaTy firstType secondType` and structural recursion on
Ty admits it; the third conjunct is weak SN on snd, because
`secondType.subst0 firstType (RawTerm.fst pairRaw)` is a
substituted Ty — same substituted-codomain wall as K12.6
piTy):

```
Reducible (Ty.sigmaTy A B) p =
  SN(p) ∧ Reducible A (Term.fst p) ∧ SN(Term.snd p)
```

The three-conjunct shape demands three independent preservation
discharges under one raw-progress step:

* **SN(p)**: pure-SN preservation, K12.20.B's raw
  `step_preserves` handles it directly.
* **Reducible A (fst p)**: needs `firstTypeCR2` hypothesis
  threaded through (the structural-recursion-on-Ty bundling
  comes later when all 15 compound CR2 arms ship as one
  bundle).  The fst-cong step lifts `rawStep` via
  `RawStep.par.fst`; distinctness via `injection` on
  `RawTerm.fst.injEq` (ctor injectivity, propext-free).
* **SN(snd p)**: pure-SN preservation again; snd-cong step
  via `RawStep.par.snd`, distinctness via `injection` on
  `RawTerm.snd.injEq`.

Term.fst's raw projection IS `RawTerm.fst` (per Term.lean:140),
Term.snd's IS `RawTerm.snd` (per Term.lean:145).  So the cong
rules `RawStep.par.fst` and `RawStep.par.snd` apply directly to
typed projections.
-/

/-- **K12.20.H sigmaTy arm**: asymmetric-closure CR2 for
`Ty.sigmaTy`.  Takes `firstTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the smaller `firstType`
sub-Ty — supplied externally per the per-arm decomposition; the
unified structurally-recursive bundling ships after all 15
compound-arm lemmas land).  Both SN conjuncts (pair + snd) are
pure-SN preservation; the middle full-Reducible conjunct uses
firstTypeCR2 with fst-cong. -/
theorem Reducible.step_preserves_sigmaTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.sigmaTy firstType secondType) sourceRaw}
    {target : Term context (Ty.sigmaTy firstType secondType) targetRaw}
    (firstTypeCR2 :
        ∀ {fstSourceRaw fstTargetRaw : RawTerm scope}
          {fstSource : Term context firstType fstSourceRaw}
          {fstTarget : Term context firstType fstTargetRaw},
          Reducible firstType fstSource →
          RawStep.parProgress fstSourceRaw fstTargetRaw →
          Reducible firstType fstTarget)
    (sourceReducible :
        Reducible (Ty.sigmaTy firstType secondType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.sigmaTy firstType secondType) target := by
  refine ⟨?_, ?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have fstStep : RawStep.parProgress
        (RawTerm.fst sourceRaw) (RawTerm.fst targetRaw) := by
      refine ⟨RawStep.par.fst rawStep.1, ?_⟩
      intro fstEq
      apply rawStep.2
      injection fstEq
    exact firstTypeCR2 sourceReducible.2.1 fstStep
  · have sndStep : RawStep.parProgress
        (RawTerm.snd sourceRaw) (RawTerm.snd targetRaw) := by
      refine ⟨RawStep.par.snd rawStep.1, ?_⟩
      intro sndEq
      apply rawStep.2
      injection sndEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.2.2 sndStep

/-! ## K12.20.I typed CR2 lift — Ty.id SN-output idJ compound arm

Fourth compound-arm CR2 lemma.  `Ty.id` ships an **SN-output idJ
closure** in K12.9:

```
Reducible (Ty.id A x y) w =
  SN(w) ∧ ∀ {M : Ty} {br} (bc : Term ctx M br),
            SN(bc) → SN(Term.idJ bc w)
```

The eliminator output is `SN(Term.idJ bc w)` not full
`Reducible motiveType (Term.idJ bc w)`.  Consequently, CR2 for
`Ty.id` needs NO recursive motiveTypeCR2 hypothesis — both
SN-of-witness and SN-of-idJ-result are pure-SN preservation,
both discharged by K12.20.B's raw `step_preserves`.  Same
SN-output pattern as K12.20.G piTy.

Term.idJ's raw projection IS `RawTerm.idJ baseRaw witnessRaw`
(per Term.lean:245), and `RawStep.par.idJ` takes paired par
steps on baseRaw + witnessRaw (per RawPar.lean:179).  For the
CR2 step, baseCase is unchanged across source/target, so the
baseRaw side gets `RawStep.par.refl baseRaw` while the witness
side gets `rawStep.1`.
-/

/-- **K12.20.I id arm**: SN-output idJ closure CR2 for `Ty.id`.  Both
SN-of-witness and SN-of-idJ-result are preserved by the same
raw `step_preserves`.  Distinctness on idJ via ctor injectivity
(injection extracts witness-side raw equality, contradicts
rawStep.2). -/
theorem Reducible.step_preserves_id
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.id carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.id carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.id carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.id carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType baseRaw baseCase baseSN
    have idJStep : RawStep.parProgress
        (RawTerm.idJ baseRaw sourceRaw)
        (RawTerm.idJ baseRaw targetRaw) := by
      refine ⟨RawStep.par.idJ (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro idJEq
      apply rawStep.2
      injection idJEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 baseCase baseSN) idJStep

/-! ## K12.20.J typed CR2 lift — Ty.listType SN-output elim compound arm

Fifth compound-arm CR2 lemma.  `Ty.listType` ships an **SN-output elim
closure** in K12.8: the eliminator output is plain SN, not full
Reducible.  Closure shape (per
Reducibility.lean:404):

```
Reducible (Ty.listType A) xs =
  SN(xs) ∧ ∀ {M} {nilRaw consRaw} (nilBranch consBranch),
    SN(nilBranch) → SN(consBranch) →
    (∀ head tail, Reducible A head → SN(tail) →
                  SN(consBranch head tail)) →
    SN(listElim xs nilBranch consBranch)
```

The branch-SN and application-closure hypotheses are propagated
unchanged by sourceReducible.2 — CR2 needs NO recursive
elementTypeCR2 hypothesis because the eliminator output is plain SN,
not Reducible.  Same weak-closure pattern as K12.20.G piTy and
K12.20.I id.

Term.listElim shares raw form `RawTerm.listElim scrutineeRaw
nilRaw consRaw` (per Term.lean:200); `RawStep.par.listElim`
takes paired par steps on all three components (per RawPar.lean:
120).  For CR2, branches are fixed across source/target, so the
nilRaw/consRaw sides get `par.refl` while scrutinee gets
`rawStep.1`.
-/

/-- **K12.20.J listType arm**: weak-elim-closure CR2 for
`Ty.listType`.  Both SN-of-listTerm and SN-of-listElim-result are
preserved by the same raw `step_preserves`.  Distinctness on
listElim via ctor injectivity (injection extracts scrutinee-side
raw equality, contradicts rawStep.2). -/
theorem Reducible.step_preserves_listType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.listType elementType) sourceRaw}
    {target : Term context (Ty.listType elementType) targetRaw}
    (sourceReducible :
        Reducible (Ty.listType elementType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.listType elementType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType nilRaw consRaw nilBranch consBranch nilSN consSN consApplied
    have listElimStep : RawStep.parProgress
        (RawTerm.listElim sourceRaw nilRaw consRaw)
        (RawTerm.listElim targetRaw nilRaw consRaw) := by
      refine ⟨RawStep.par.listElim rawStep.1
          (RawStep.par.refl nilRaw) (RawStep.par.refl consRaw), ?_⟩
      intro listElimEq
      apply rawStep.2
      injection listElimEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 nilBranch consBranch nilSN consSN consApplied)
      listElimStep

/-! ## K12.20.K typed CR2 lift — Ty.optionType weak-elim-closure compound arm

Sixth compound-arm CR2 lemma.  `Ty.optionType` ships a **weak
elim closure** in K12.8, cleanest of the three K12.8 parametric
arms: someBranch's type matches K12.6 piTy weak shape exactly
when restricted to elementType.  Closure shape (per
Reducibility.lean:426):

```
Reducible (Ty.optionType A) o =
  SN(o) ∧ ∀ {M} {noneRaw someRaw} (noneBranch someBranch),
    SN(noneBranch) → SN(someBranch) →
    (∀ v, Reducible A v → SN(Term.app someBranch v)) →
    SN(optionMatch o noneBranch someBranch)
```

Same mechanical shape as K12.20.J listType — eliminator output
is plain SN, NO recursive elementTypeCR2 hypothesis needed.
Term.optionMatch raw form is `RawTerm.optionMatch scrutineeRaw
noneRaw someRaw` (per Term.lean:216); `RawStep.par.optionMatch`
takes triple par steps (per RawPar.lean:136).  For CR2 the
branches use `par.refl` while scrutinee gets `rawStep.1`.
-/

/-- **K12.20.K optionType arm**: weak-elim-closure CR2 for
`Ty.optionType`.  Both SN-of-optionTerm and SN-of-optionMatch-
result are preserved by the same raw `step_preserves`.
Distinctness on optionMatch via ctor injectivity. -/
theorem Reducible.step_preserves_optionType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.optionType elementType) sourceRaw}
    {target : Term context (Ty.optionType elementType) targetRaw}
    (sourceReducible :
        Reducible (Ty.optionType elementType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.optionType elementType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType noneRaw someRaw noneBranch someBranch noneSN someSN someApplied
    have optionMatchStep : RawStep.parProgress
        (RawTerm.optionMatch sourceRaw noneRaw someRaw)
        (RawTerm.optionMatch targetRaw noneRaw someRaw) := by
      refine ⟨RawStep.par.optionMatch rawStep.1
          (RawStep.par.refl noneRaw) (RawStep.par.refl someRaw), ?_⟩
      intro optionMatchEq
      apply rawStep.2
      injection optionMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 noneBranch someBranch noneSN someSN someApplied)
      optionMatchStep

/-! ## K12.20.L typed CR2 lift — Ty.eitherType symmetric SN-output elim compound arm

Seventh compound-arm CR2 lemma.  `Ty.eitherType` ships a
**symmetric SN-output elim closure** in K12.8: both `leftType` and
`rightType` are strict sub-Ty of `Ty.eitherType leftType
rightType`, so each branch's arrow shape matches K12.6 piTy SN-output
closure per side.  Closure shape (per Reducibility.lean:446):

```
Reducible (Ty.eitherType A B) e =
  SN(e) ∧ ∀ {M} {leftRaw rightRaw} (leftBranch rightBranch),
    SN(leftBranch) → SN(rightBranch) →
    (∀ v, Reducible A v → SN(Term.app leftBranch v)) →
    (∀ v, Reducible B v → SN(Term.app rightBranch v)) →
    SN(eitherMatch e leftBranch rightBranch)
```

Same mechanical shape as K12.20.J listType / K12.20.K
optionType — eliminator output is plain SN, NO recursive
leftTypeCR2 / rightTypeCR2 hypothesis needed.  Term.eitherMatch
raw form is `RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw`
(per Term.lean:234); `RawStep.par.eitherMatch` takes triple par
steps (per RawPar.lean:159).  For CR2 the branches use
`par.refl` while scrutinee gets `rawStep.1`.
-/

/-- **K12.20.L eitherType arm**: symmetric-weak-elim-closure CR2
for `Ty.eitherType`.  Both SN-of-eitherTerm and SN-of-eitherMatch-
result are preserved by the same raw `step_preserves`.
Distinctness on eitherMatch via ctor injectivity. -/
theorem Reducible.step_preserves_eitherType
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.eitherType leftType rightType) sourceRaw}
    {target : Term context (Ty.eitherType leftType rightType) targetRaw}
    (sourceReducible :
        Reducible (Ty.eitherType leftType rightType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.eitherType leftType rightType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType leftRaw rightRaw leftBranch rightBranch
      leftSN rightSN leftApplied rightApplied
    have eitherMatchStep : RawStep.parProgress
        (RawTerm.eitherMatch sourceRaw leftRaw rightRaw)
        (RawTerm.eitherMatch targetRaw leftRaw rightRaw) := by
      refine ⟨RawStep.par.eitherMatch rawStep.1
          (RawStep.par.refl leftRaw) (RawStep.par.refl rightRaw), ?_⟩
      intro eitherMatchEq
      apply rawStep.2
      injection eitherMatchEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 leftBranch rightBranch leftSN rightSN
        leftApplied rightApplied)
      eitherMatchStep

/-! ## K12.20.M typed CR2 lift — Ty.path strong-pathApp-closure compound arm

Eighth compound-arm CR2 lemma.  `Ty.path` ships a **strong
pathApp closure** in K12.12: the eliminator produces a full
`Reducible carrier _` verdict (NOT plain SN), because `carrier`
is a strict sub-Ty of `Ty.path carrier left right` and the
structural-recursion-on-Ty checker admits `Reducible carrier`
recursion.  Closure shape (per Reducibility.lean:476):

```
Reducible (Ty.path A x y) p =
  SN(p) ∧ ∀ (modeIsUnivalent : mode = Mode.univalent)
            {intervalRaw} (intervalTerm : Term context Ty.interval intervalRaw),
    SN(intervalTerm) →
    Reducible A (Term.pathApp modeIsUnivalent p intervalTerm)
```

This is the **strong** pattern from K12.20.F arrow: full
Reducible eliminator output forces an explicit `carrierCR2`
hypothesis to lift Reducible across the cong step.  The interval
side stays SN-only (Ty.interval is a sibling Ty constructor, not
a strict sub-Ty of Ty.path — K12.4's closed-leaf arm gives
`Reducible Ty.interval _ = Term.isStronglyNormalizing _`
propositionally, so SN demotion preserves Tait semantics).

Term.pathApp raw form is `RawTerm.pathApp pathRaw intervalRaw`
(per Term.lean:355); `RawStep.par.pathAppCong` takes paired par
steps (per RawPar.lean:558).  For CR2, interval side gets
`par.refl` while path side gets `rawStep.1`.  Distinctness via
`injection` on RawTerm.pathApp.injEq.
-/

/-- **K12.20.M path arm**: strong-pathApp-closure CR2 for
`Ty.path`.  Takes `carrierCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`carrierType`).  SN-of-pathTerm preserved by raw `step_preserves`;
the full-Reducible pathApp conjunct lifted via carrierCR2 over
the pathAppCong step. -/
theorem Reducible.step_preserves_path
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.path carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.path carrierType leftEndpoint rightEndpoint) targetRaw}
    (carrierCR2 :
        ∀ {pathAppSourceRaw pathAppTargetRaw : RawTerm scope}
          {pathAppSource : Term context carrierType pathAppSourceRaw}
          {pathAppTarget : Term context carrierType pathAppTargetRaw},
          Reducible carrierType pathAppSource →
          RawStep.parProgress pathAppSourceRaw pathAppTargetRaw →
          Reducible carrierType pathAppTarget)
    (sourceReducible :
        Reducible (Ty.path carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.path carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsUnivalent intervalRaw intervalTerm intervalSN
    have pathAppStep : RawStep.parProgress
        (RawTerm.pathApp sourceRaw intervalRaw)
        (RawTerm.pathApp targetRaw intervalRaw) := by
      refine ⟨RawStep.par.pathAppCong rawStep.1 (RawStep.par.refl intervalRaw), ?_⟩
      intro pathAppEq
      apply rawStep.2
      injection pathAppEq
    exact carrierCR2
      (sourceReducible.2 modeIsUnivalent intervalTerm intervalSN) pathAppStep

/-! ## K12.20.N typed CR2 lift — Ty.glue strong-glueElim-closure compound arm

Ninth compound-arm CR2 lemma.  `Ty.glue` ships a **strong
glueElim closure** in K12.12: the eliminator produces a full
`Reducible baseType _` verdict (NOT plain SN), because
`baseType` is a strict sub-Ty of `Ty.glue baseType
boundaryWitness` and the structural-recursion-on-Ty checker
admits `Reducible baseType` recursion.  Closure shape (per
Reducibility.lean:491):

```
Reducible (Ty.glue baseType _) gluedValue =
  SN(gluedValue) ∧
  ∀ (modeIsUnivalent : mode = Mode.univalent),
    Reducible baseType
      (Term.glueElim modeIsUnivalent gluedValue)
```

This is the **strong** pattern (mirror of K12.20.F arrow and
K12.20.M path), but **even simpler than path** — no quantifier
over an interval argument, no SN-on-arg conjunct.  Just the
mode-univalent witness binder.  The proof carries an explicit
`baseTypeCR2` hypothesis to lift Reducible across the cong step.

Term.glueElim raw form is `RawTerm.glueElim gluedRaw` (per
Term.lean:373); `RawStep.par.glueElimCong` is a 1-arg cong rule
taking just `gluedRawStep` (per RawPar.lean:633-638).  No paired
substituent: glueElim has only one argument.  Distinctness via
`injection` on `RawTerm.glueElim.injEq`.
-/

/-- **K12.20.N glue arm**: strong-glueElim-closure CR2 for
`Ty.glue`.  Takes `baseTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`baseType`).  SN-of-gluedTerm preserved by raw `step_preserves`;
the full-Reducible glueElim conjunct lifted via baseTypeCR2 over
the glueElimCong step.  Simpler than K12.20.M path — single-
ctor cong rule, no interval binder. -/
theorem Reducible.step_preserves_glue
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.glue baseType boundaryWitness) sourceRaw}
    {target : Term context (Ty.glue baseType boundaryWitness) targetRaw}
    (baseTypeCR2 :
        ∀ {glueElimSourceRaw glueElimTargetRaw : RawTerm scope}
          {glueElimSource : Term context baseType glueElimSourceRaw}
          {glueElimTarget : Term context baseType glueElimTargetRaw},
          Reducible baseType glueElimSource →
          RawStep.parProgress glueElimSourceRaw glueElimTargetRaw →
          Reducible baseType glueElimTarget)
    (sourceReducible :
        Reducible (Ty.glue baseType boundaryWitness) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.glue baseType boundaryWitness) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsUnivalent
    have glueElimStep : RawStep.parProgress
        (RawTerm.glueElim sourceRaw)
        (RawTerm.glueElim targetRaw) := by
      refine ⟨RawStep.par.glueElimCong rawStep.1, ?_⟩
      intro glueElimEq
      apply rawStep.2
      injection glueElimEq
    exact baseTypeCR2
      (sourceReducible.2 modeIsUnivalent) glueElimStep

/-! ## K12.20.O typed CR2 lift — Ty.oeq SN-output oeqJ compound arm

Tenth compound-arm CR2 lemma.  `Ty.oeq` (HoTT observational
equality) ships an **SN-output oeqJ closure** in K12.10: the
eliminator output is plain SN, not full `Reducible motiveType _`.
The arbitrary `motiveType` is NOT a strict sub-Ty of
`Ty.oeq carrier left right` — structural-recursion-on-Ty would
not admit a `Reducible motiveType` recursive call (K12.6 / K12.9
SN-output pattern, identical to K12.20.I for Ty.id and the parametric
inductive SN-output elim arms K12.20.J/K/L).  Closure shape (per
Reducibility.lean:503-509):

```
Reducible (Ty.oeq _ _ _) witness =
  SN(witness) ∧
  ∀ {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw),
    SN baseCase →
    SN (Term.oeqJ baseCase witness)
```

SN-output closure → **no recursive hypothesis needed**.  Eliminator
output is SN, so the cong lift goes via
`RawTerm.isStronglyNormalizing.step_preserves` directly.

Term.oeqJ raw form is `RawTerm.oeqJ baseRaw witnessRaw` (per
Term.lean:261); `RawStep.par.oeqJCong` takes paired par steps
on baseCase + witness (per RawPar.lean:705-710).  For CR2 the
baseCase rides `par.refl` (not progressing); witness rides
`rawStep.1`.  Distinctness via `injection` on
`RawTerm.oeqJ.injEq`.
-/

/-- **K12.20.O oeq arm**: SN-output oeqJ closure CR2 for `Ty.oeq`.
No recursive hypothesis needed (SN-output closure produces SN,
not Reducible).  SN-of-witnessTerm preserved by raw
`step_preserves`; SN-of-oeqJ-applied lifted via raw
`step_preserves` over the oeqJCong step.  Mirror of K12.20.I id
arm; differs only in the raw cong rule name (`oeqJCong` rather
than `idJ`). -/
theorem Reducible.step_preserves_oeq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.oeq carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.oeq carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.oeq carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro motiveType baseRaw baseCase baseSN
    have oeqJStep : RawStep.parProgress
        (RawTerm.oeqJ baseRaw sourceRaw)
        (RawTerm.oeqJ baseRaw targetRaw) := by
      refine ⟨RawStep.par.oeqJCong (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro oeqJEq
      apply rawStep.2
      injection oeqJEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 baseCase baseSN) oeqJStep

/-! ## K12.20.P typed CR2 lift — Ty.idStrict weak-idStrictRec-closure compound arm

Eleventh compound-arm CR2 lemma.  `Ty.idStrict` (strict identity
type) ships a **weak idStrictRec closure** in K12.10: the
eliminator output is plain SN, not full `Reducible motiveType _`.
The arbitrary `motiveType` is NOT a strict sub-Ty of
`Ty.idStrict carrier left right` — structural-recursion-on-Ty
cannot recurse `Reducible motiveType`.  Same K12.6 / K12.9 weak-J
pattern as K12.20.I (id) and K12.20.O (oeq).

Closure shape (per Reducibility.lean:517-525):

```
Reducible (Ty.idStrict _ _ _) witness =
  SN(witness) ∧
  ∀ (modeIsStrict : mode = Mode.strict)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw),
    SN baseCase →
    SN (Term.idStrictRec modeIsStrict baseCase witness)
```

When `mode ≠ Mode.strict` the binder is uninhabited and the
inner ∀ is vacuous (closure reduces to SN(witness) alone) —
matches the conditional-elim K12.10 idStrict pattern.

Weak closure → **no recursive hypothesis needed**.  Eliminator
output is SN, so the cong lift goes via
`RawTerm.isStronglyNormalizing.step_preserves` directly.

Term.idStrictRec raw form is `RawTerm.idStrictRec baseRaw
witnessRaw` (per Term.lean:294) — the `modeIsStrict` proof lives
at the typed level only.  `RawStep.par.idStrictRecCong` takes
paired par steps on baseCase + witness (per RawPar.lean:724-729).
For CR2 the baseCase rides `par.refl`; witness rides `rawStep.1`.
Distinctness via `injection` on `RawTerm.idStrictRec.injEq`.
-/

/-- **K12.20.P idStrict arm**: SN-output idStrictRec closure CR2 for
`Ty.idStrict`.  No recursive hypothesis needed (SN-output
closure produces SN, not Reducible).  Identical structure to
K12.20.O oeq, with extra `modeIsStrict` binder threaded through
the per-mode quantifier in the closure body. -/
theorem Reducible.step_preserves_idStrict
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context
        (Ty.idStrict carrierType leftEndpoint rightEndpoint) sourceRaw}
    {target : Term context
        (Ty.idStrict carrierType leftEndpoint rightEndpoint) targetRaw}
    (sourceReducible :
        Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.idStrict carrierType leftEndpoint rightEndpoint) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro modeIsStrict motiveType baseRaw baseCase baseSN
    have idStrictRecStep : RawStep.parProgress
        (RawTerm.idStrictRec baseRaw sourceRaw)
        (RawTerm.idStrictRec baseRaw targetRaw) := by
      refine ⟨RawStep.par.idStrictRecCong
        (RawStep.par.refl baseRaw) rawStep.1, ?_⟩
      intro idStrictRecEq
      apply rawStep.2
      injection idStrictRecEq
    exact RawTerm.isStronglyNormalizing.step_preserves
      (sourceReducible.2 modeIsStrict baseCase baseSN) idStrictRecStep

/-! ## K12.20.Q typed CR2 lift — Ty.equiv strong-equivApp-closure compound arm

Twelfth compound-arm CR2 lemma.  `Ty.equiv carrierA carrierB`
(type equivalence) ships a **strong equivApp closure** in K12.11:
the eliminator produces full `Reducible carrierB (Term.equivApp
equivTerm argumentTerm)`.  BOTH `carrierA` and `carrierB` are
strict sub-Ty of `Ty.equiv carrierA carrierB` — structural-
recursion-on-Ty admits `Reducible carrierA` AND `Reducible
carrierB` recursive calls (K12.5 RC.arrow shape).

Closure shape (per Reducibility.lean:537-542):

```
Reducible (Ty.equiv carrierA carrierB) equivTerm =
  SN(equivTerm) ∧
  ∀ {argumentRaw : RawTerm scope}
    (argumentTerm : Term context carrierA argumentRaw),
    Reducible carrierA argumentTerm →
    Reducible carrierB
      (Term.equivApp equivTerm argumentTerm)
```

Structurally identical to K12.20.F arrow: `SN(f) ∧ ∀ arg,
Reducible A arg → Reducible B (Term.app f arg)`.  The argument
side stays at carrierA — it rides `par.refl` through the cong
step and does NOT progress.  Only `equivTerm` progresses; the
eliminator output is at carrierB, so the proof carries an
explicit `carrierBCR2` hypothesis to lift Reducible over the
equivAppCong step.  No `carrierACR2` is needed — that side never
moves in this cong step.

Term.equivApp raw form is `RawTerm.equivApp equivRaw argumentRaw`
(per Term.lean:727); `RawStep.par.equivAppCong` takes paired par
steps on equiv + argument (per RawPar.lean:738-743).  For CR2
the equiv side rides `rawStep.1`; argument side rides
`par.refl`.  Distinctness via `injection` on
`RawTerm.equivApp.injEq`.
-/

/-- **K12.20.Q equiv arm**: strong-equivApp-closure CR2 for
`Ty.equiv`.  Takes `carrierBCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`carrierB`).  SN-of-equivTerm preserved by raw `step_preserves`;
the full-Reducible equivApp conjunct lifted via carrierBCR2 over
the equivAppCong step.  Structurally identical to K12.20.F arrow;
differs only in raw cong rule name (`equivAppCong` vs `app`) and
ctor (`equivApp` vs `app`). -/
theorem Reducible.step_preserves_equiv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.equiv carrierA carrierB) sourceRaw}
    {target : Term context (Ty.equiv carrierA carrierB) targetRaw}
    (carrierBCR2 :
        ∀ {equivAppSourceRaw equivAppTargetRaw : RawTerm scope}
          {equivAppSource : Term context carrierB equivAppSourceRaw}
          {equivAppTarget : Term context carrierB equivAppTargetRaw},
          Reducible carrierB equivAppSource →
          RawStep.parProgress equivAppSourceRaw equivAppTargetRaw →
          Reducible carrierB equivAppTarget)
    (sourceReducible :
        Reducible (Ty.equiv carrierA carrierB) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.equiv carrierA carrierB) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · intro argumentRaw argumentTerm argumentReducible
    have equivAppStep : RawStep.parProgress
        (RawTerm.equivApp sourceRaw argumentRaw)
        (RawTerm.equivApp targetRaw argumentRaw) := by
      refine ⟨RawStep.par.equivAppCong rawStep.1
        (RawStep.par.refl argumentRaw), ?_⟩
      intro equivAppEq
      apply rawStep.2
      injection equivAppEq
    exact carrierBCR2
      (sourceReducible.2 argumentTerm argumentReducible) equivAppStep

/-! ## K12.20.R typed CR2 lift — Ty.refine strong-refineElim-closure compound arm

Thirteenth compound-arm CR2 lemma.  `Ty.refine baseType
predicate` ships a **strong refineElim closure** in K12.14:
the eliminator produces full `Reducible baseType (Term.refineElim
refinedValue)` from the simple projection.  `baseType` is a
strict sub-Ty of `Ty.refine baseType predicate` — structural-
recursion-on-Ty admits `Reducible baseType` recursive call.
The `predicate : RawTerm (scope+1)` is a RawTerm-binder with no
typed dependency at the Reducible layer; the "Decidable
predicate discharge" aspect of K12.14 lives at Layer 5 SMT-
recheck (#1342 D5.6, #1344 D5.8) and is orthogonal to the
Reducibility-candidate closure shipped here.

Closure shape (per Reducibility.lean:554-556):

```
Reducible (Ty.refine baseType _) refinedValue =
  SN(refinedValue) ∧
  Reducible baseType (Term.refineElim refinedValue)
```

This is the **simplest** strong compound arm of the 15.  No
quantifier overhead, no mode-univalent / mode-strict witness,
no interval / motive binder.  Pure projection — directly
analogous to K12.20.N glue but stripped down further (no
modeIsUnivalent binder).

Term.refineElim raw form is `RawTerm.refineElim refinedRaw`
(per Term.lean:446); `RawStep.par.refineElimCong` is a 1-arg
cong rule taking just `refinedRawStep` (per RawPar.lean:766-771).
Single-substituent ctor → no `par.refl` companion needed.
Distinctness via `injection` on `RawTerm.refineElim.injEq`.
-/

/-- **K12.20.R refine arm**: strong-refineElim-closure CR2 for
`Ty.refine`.  Takes `baseTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`baseType`).  SN-of-refinedValue preserved by raw
`step_preserves`; the full-Reducible refineElim conjunct lifted
via baseTypeCR2 over the refineElimCong step.  Simplest strong
compound arm — no quantifier, no mode binder. -/
theorem Reducible.step_preserves_refine
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.refine baseType predicate) sourceRaw}
    {target : Term context (Ty.refine baseType predicate) targetRaw}
    (baseTypeCR2 :
        ∀ {refineElimSourceRaw refineElimTargetRaw : RawTerm scope}
          {refineElimSource : Term context baseType refineElimSourceRaw}
          {refineElimTarget : Term context baseType refineElimTargetRaw},
          Reducible baseType refineElimSource →
          RawStep.parProgress refineElimSourceRaw refineElimTargetRaw →
          Reducible baseType refineElimTarget)
    (sourceReducible :
        Reducible (Ty.refine baseType predicate) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.refine baseType predicate) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have refineElimStep : RawStep.parProgress
        (RawTerm.refineElim sourceRaw)
        (RawTerm.refineElim targetRaw) := by
      refine ⟨RawStep.par.refineElimCong rawStep.1, ?_⟩
      intro refineElimEq
      apply rawStep.2
      injection refineElimEq
    exact baseTypeCR2 sourceReducible.2 refineElimStep

/-! ## K12.20.S typed CR2 lift — Ty.record strong-recordProj-closure compound arm

Fourteenth compound-arm CR2 lemma.  `Ty.record singleFieldType`
ships a **strong recordProj closure** in K12.15: the eliminator
produces full `Reducible singleFieldType (Term.recordProj
recordValue)` from the simple projection.  `singleFieldType` is
a strict sub-Ty of `Ty.record singleFieldType` — structural-
recursion-on-Ty admits `Reducible singleFieldType` recursive
call.  Multi-field records compose via nested single-field
records (per Term.lean docstring), preserving this closure
shape under nesting.

Closure shape (per Reducibility.lean:563-565):

```
Reducible (Ty.record singleFieldType) recordValue =
  SN(recordValue) ∧
  Reducible singleFieldType (Term.recordProj recordValue)
```

Structurally identical to K12.20.R refine: pure projection,
single-substituent cong rule, no quantifier overhead.  Only
differences: ctor name (`Ty.record` vs `Ty.refine`), eliminator
(`recordProj` vs `refineElim`), strict-sub-Ty field name
(`singleFieldType` vs `baseType`).  No predicate binder (record
has no SMT-recheck axis — purely structural).

Term.recordProj raw form is `RawTerm.recordProj recordRaw` (per
Term.lean:425); `RawStep.par.recordProjCong` is a 1-arg cong
rule (per RawPar.lean:790-795).  Distinctness via `injection`
on `RawTerm.recordProj.injEq`.
-/

/-- **K12.20.S record arm**: strong-recordProj-closure CR2 for
`Ty.record`.  Takes `singleFieldTypeCR2` as explicit hypothesis
(the recursive Reducible-preservation witness on the strict
sub-Ty `singleFieldType`).  SN-of-recordValue preserved by raw
`step_preserves`; the full-Reducible recordProj conjunct lifted
via singleFieldTypeCR2 over the recordProjCong step.  Mirror of
K12.20.R refine. -/
theorem Reducible.step_preserves_record
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.record singleFieldType) sourceRaw}
    {target : Term context (Ty.record singleFieldType) targetRaw}
    (singleFieldTypeCR2 :
        ∀ {recordProjSourceRaw recordProjTargetRaw : RawTerm scope}
          {recordProjSource :
              Term context singleFieldType recordProjSourceRaw}
          {recordProjTarget :
              Term context singleFieldType recordProjTargetRaw},
          Reducible singleFieldType recordProjSource →
          RawStep.parProgress recordProjSourceRaw recordProjTargetRaw →
          Reducible singleFieldType recordProjTarget)
    (sourceReducible : Reducible (Ty.record singleFieldType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.record singleFieldType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have recordProjStep : RawStep.parProgress
        (RawTerm.recordProj sourceRaw)
        (RawTerm.recordProj targetRaw) := by
      refine ⟨RawStep.par.recordProjCong rawStep.1, ?_⟩
      intro recordProjEq
      apply rawStep.2
      injection recordProjEq
    exact singleFieldTypeCR2 sourceReducible.2 recordProjStep

/-! ## K12.20.T typed CR2 lift — Ty.codata strong-codataDest-closure compound arm

Fifteenth (and final) compound-arm CR2 lemma.  `Ty.codata
stateType outputType` ships a **strong codataDest closure** in
K12.15: the eliminator produces full `Reducible outputType
(Term.codataDest codataValue)` from the observation projection.
`outputType` is a strict sub-Ty of `Ty.codata stateType
outputType` — structural-recursion-on-Ty admits the recursive
`Reducible outputType` call.

Closure shape (per Reducibility.lean:574-576):

```
Reducible (Ty.codata _ outputType) codataValue =
  SN(codataValue) ∧
  Reducible outputType (Term.codataDest codataValue)
```

Note: `stateType` is also a strict sub-Ty of `Ty.codata
stateType outputType`, but the closure does NOT recurse on it
— the stateType is packed into the unfold/initial-state and is
never exposed by an eliminator.  Productivity-checking at higher
observation depths lives at the codata-corecursion Layer (#1267
K08), orthogonal to this RC closure.  So this lemma needs only
ONE recursive-CR2 hypothesis (`outputTypeCR2`).

Structurally identical to K12.20.{R refine, S record}: pure
projection, single-substituent cong rule, no quantifier
overhead.  Only differences: ctor name (`Ty.codata` takes two
Ty args — `stateType` carried implicit, only `outputType`
appears in the recursive hypothesis), eliminator
(`codataDest` vs `recordProj`).

Term.codataDest raw form is `RawTerm.codataDest codataRaw` (per
Term.lean:460-465); `RawStep.par.codataDestCong` is a 1-arg
cong rule (per RawPar.lean:820-825).  Distinctness via
`injection` on `RawTerm.codataDest.injEq`.

**Compound-arm CR2 sweep COMPLETE** with this lemma: all 15
compound-arm closures shipped (arrow / piTy / sigmaTy / id /
listType / optionType / eitherType / path / glue / oeq /
idStrict / equiv / refine / record / codata).  Next: K12.20
wrap-up combining all 25 arms (10 SN-direct + 15 compound) into
a single structurally-recursive `Reducible.step_preserves`.
-/

/-- **K12.20.T codata arm**: strong-codataDest-closure CR2 for
`Ty.codata`.  Takes `outputTypeCR2` as explicit hypothesis (the
recursive Reducible-preservation witness on the strict sub-Ty
`outputType` — the projection target).  SN-of-codataValue
preserved by raw `step_preserves`; the full-Reducible
codataDest conjunct lifted via outputTypeCR2 over the
codataDestCong step.  Mirror of K12.20.{R refine, S record}.
The `stateType` index is carried implicit and never reached —
codata's state is packed into the unfold/initial-state, not
exposed by any current eliminator. -/
theorem Reducible.step_preserves_codata
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {source : Term context (Ty.codata stateType outputType) sourceRaw}
    {target : Term context (Ty.codata stateType outputType) targetRaw}
    (outputTypeCR2 :
        ∀ {codataDestSourceRaw codataDestTargetRaw : RawTerm scope}
          {codataDestSource :
              Term context outputType codataDestSourceRaw}
          {codataDestTarget :
              Term context outputType codataDestTargetRaw},
          Reducible outputType codataDestSource →
          RawStep.parProgress codataDestSourceRaw codataDestTargetRaw →
          Reducible outputType codataDestTarget)
    (sourceReducible :
        Reducible (Ty.codata stateType outputType) source)
    (rawStep : RawStep.parProgress sourceRaw targetRaw) :
    Reducible (Ty.codata stateType outputType) target := by
  refine ⟨?_, ?_⟩
  · exact RawTerm.isStronglyNormalizing.step_preserves
      sourceReducible.1 rawStep
  · have codataDestStep : RawStep.parProgress
        (RawTerm.codataDest sourceRaw)
        (RawTerm.codataDest targetRaw) := by
      refine ⟨RawStep.par.codataDestCong rawStep.1, ?_⟩
      intro codataDestEq
      apply rawStep.2
      injection codataDestEq
    exact outputTypeCR2 sourceReducible.2 codataDestStep


end LeanFX2
