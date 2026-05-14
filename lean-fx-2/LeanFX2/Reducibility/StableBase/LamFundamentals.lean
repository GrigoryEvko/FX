import LeanFX2.Reducibility.StableBase.ClosedWeakens

/-! # LeanFX2.Reducibility.StableBase.LamFundamentals

K12.20.U3.monotone projection arms for `Ty.sigmaTy` / `Ty.glue`
/ `Ty.refine` / `Ty.record` / `Ty.codata` (compound weakening),
plus the `RawTerm.app_lam_isStronglyNormalizing` + Term wrapper
+ the `Reducible.fundamental_lam_at_arrow_*` headlines.

## Root status

Layer 3 metatheory leaf.  Second slice of K12.20.U4 stable base. -/

namespace LeanFX2


/-- **K12.20.U3.monotone projection arm**: sigma reducibility weakens
when the first projection's reducibility weakens at the strict
sub-type.  The second projection is SN-only in the current K12.7
closure, so the raw SN weakening wrapper handles it directly. -/
theorem Reducible.weaken_sigmaTy
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.sigmaTy firstType secondType) sourceRaw}
    (firstTypeWeaken :
      ∀ {firstRaw : RawTerm scope}
        {firstTerm : Term context firstType firstRaw},
        Reducible firstType firstTerm →
        Reducible firstType.weaken (Term.weaken newType firstTerm))
    (sourceReducible : Reducible (Ty.sigmaTy firstType secondType) sourceTerm) :
    Reducible ((Ty.sigmaTy firstType secondType).weaken)
      (Term.weaken newType sourceTerm) :=
  ⟨Term.isStronglyNormalizing_weaken (newType := newType) sourceReducible.1,
   firstTypeWeaken sourceReducible.2.1,
   Term.isStronglyNormalizing_weaken (newType := newType) sourceReducible.2.2⟩

/-- **K12.20.U3.monotone projection arm**: glue reducibility weakens
when the base projection's reducibility weakens at the strict sub-type. -/
theorem Reducible.weaken_glue
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType baseType : Ty level scope}
    {boundaryWitness sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.glue baseType boundaryWitness) sourceRaw}
    (baseTypeWeaken :
      ∀ {baseRaw : RawTerm scope}
        {baseTerm : Term context baseType baseRaw},
        Reducible baseType baseTerm →
        Reducible baseType.weaken (Term.weaken newType baseTerm))
    (sourceReducible : Reducible (Ty.glue baseType boundaryWitness) sourceTerm) :
    Reducible ((Ty.glue baseType boundaryWitness).weaken)
      (Term.weaken newType sourceTerm) :=
  ⟨Term.isStronglyNormalizing_weaken (newType := newType) sourceReducible.1,
   fun modeIsUnivalent => baseTypeWeaken (sourceReducible.2 modeIsUnivalent)⟩

/-- **K12.20.U3.monotone projection arm**: refinement reducibility
weakens when the base projection's reducibility weakens at the strict
sub-type. -/
theorem Reducible.weaken_refine
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.refine baseType predicate) sourceRaw}
    (baseTypeWeaken :
      ∀ {baseRaw : RawTerm scope}
        {baseTerm : Term context baseType baseRaw},
        Reducible baseType baseTerm →
        Reducible baseType.weaken (Term.weaken newType baseTerm))
    (sourceReducible : Reducible (Ty.refine baseType predicate) sourceTerm) :
    Reducible ((Ty.refine baseType predicate).weaken)
      (Term.weaken newType sourceTerm) :=
  ⟨Term.isStronglyNormalizing_weaken (newType := newType) sourceReducible.1,
   baseTypeWeaken sourceReducible.2⟩

/-- **K12.20.U3.monotone projection arm**: record reducibility weakens
when the single-field projection's reducibility weakens at the strict
sub-type. -/
theorem Reducible.weaken_record
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType singleFieldType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.record singleFieldType) sourceRaw}
    (singleFieldWeaken :
      ∀ {fieldRaw : RawTerm scope}
        {fieldTerm : Term context singleFieldType fieldRaw},
        Reducible singleFieldType fieldTerm →
        Reducible singleFieldType.weaken (Term.weaken newType fieldTerm))
    (sourceReducible : Reducible (Ty.record singleFieldType) sourceTerm) :
    Reducible ((Ty.record singleFieldType).weaken)
      (Term.weaken newType sourceTerm) :=
  ⟨Term.isStronglyNormalizing_weaken (newType := newType) sourceReducible.1,
   singleFieldWeaken sourceReducible.2⟩

/-- **K12.20.U3.monotone projection arm**: codata reducibility weakens
when the destructor output's reducibility weakens at the strict sub-type. -/
theorem Reducible.weaken_codata
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType stateType outputType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.codata stateType outputType) sourceRaw}
    (outputTypeWeaken :
      ∀ {outputRaw : RawTerm scope}
        {outputTerm : Term context outputType outputRaw},
        Reducible outputType outputTerm →
        Reducible outputType.weaken (Term.weaken newType outputTerm))
    (sourceReducible : Reducible (Ty.codata stateType outputType) sourceTerm) :
    Reducible ((Ty.codata stateType outputType).weaken)
      (Term.weaken newType sourceTerm) :=
  ⟨Term.isStronglyNormalizing_weaken (newType := newType) sourceReducible.1,
   outputTypeWeaken sourceReducible.2⟩

/-- Head-β SN expansion for non-dependent application.

If the lambda body, argument, and β-contractum are all strongly
normalizing, then the whole redex `app (lam body) argument` is strongly
normalizing.  Congruence reducts recurse through body/argument SN.
The β arm is not dismissed syntactically: `RawStep.par.app_inv` may
produce a deep β target after the function side parallel-reduces to a
lambda, so the proof uses `RawStep.par.subst0_par` to relate the
original contractum to that β target and then applies raw CR2. -/
theorem RawTerm.app_lam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    ∀ {argument : RawTerm scope},
      RawTerm.isStronglyNormalizing argument →
      RawTerm.isStronglyNormalizing (body.subst0 argument) →
      RawTerm.isStronglyNormalizing
        (RawTerm.app (RawTerm.lam body) argument) := by
  induction bodyIsSN with
  | intro currentBody bodyClosure bodyIH =>
    intro argument argumentIsSN betaContractumIsSN
    induction argumentIsSN with
    | intro currentArgument argumentClosure argumentIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.app (RawTerm.lam currentBody) currentArgument) ?_
      intro target progressStep
      rcases RawStep.par.app_inv progressStep.1 with
        ⟨functionTarget, argumentTarget, targetEq,
          functionStep, argumentStep⟩
        | ⟨bodyTarget, argumentTarget, targetEq,
            functionStep, argumentStep⟩
      · obtain ⟨bodyTarget, functionTargetEq, bodyStep⟩ :=
          RawStep.par.lam_inv functionStep
        subst functionTargetEq
        subst targetEq
        by_cases bodyEq : currentBody = bodyTarget
        · subst bodyEq
          by_cases argumentEq : currentArgument = argumentTarget
          · subst argumentEq
            exact False.elim (progressStep.2 rfl)
          · have argumentContractumIsSN :
                RawTerm.isStronglyNormalizing
                  (currentBody.subst0 argumentTarget) := by
              by_cases contractumEq :
                  currentBody.subst0 currentArgument =
                    currentBody.subst0 argumentTarget
              · rw [← contractumEq]
                exact betaContractumIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  betaContractumIsSN
                  ⟨RawStep.par.subst0_par (RawStep.par.refl currentBody)
                    argumentStep, contractumEq⟩
            exact argumentIH argumentTarget ⟨argumentStep, argumentEq⟩
              argumentContractumIsSN
        · have bodyProgress :
              RawStep.parProgress currentBody bodyTarget :=
            ⟨bodyStep, bodyEq⟩
          have argumentTargetIsSN :
              RawTerm.isStronglyNormalizing argumentTarget := by
            by_cases argumentEq : currentArgument = argumentTarget
            · subst argumentEq
              exact RawTerm.isStronglyNormalizing.intro
                currentArgument argumentClosure
            · exact argumentClosure argumentTarget ⟨argumentStep, argumentEq⟩
          have bodyTargetContractumIsSN :
              RawTerm.isStronglyNormalizing
                (bodyTarget.subst0 argumentTarget) := by
            by_cases contractumEq :
                currentBody.subst0 currentArgument =
                  bodyTarget.subst0 argumentTarget
            · rw [← contractumEq]
              exact betaContractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                betaContractumIsSN
                ⟨RawStep.par.subst0_par bodyStep argumentStep,
                  contractumEq⟩
          exact bodyIH bodyTarget bodyProgress argumentTargetIsSN
            bodyTargetContractumIsSN
      · obtain ⟨bodyTargetFromLam, lamTargetEq, bodyStep⟩ :=
          RawStep.par.lam_inv functionStep
        cases lamTargetEq
        subst targetEq
        by_cases contractumEq :
            currentBody.subst0 currentArgument =
              bodyTarget.subst0 argumentTarget
        · rw [← contractumEq]
          exact betaContractumIsSN
        · exact RawTerm.isStronglyNormalizing.step_preserves
            betaContractumIsSN
            ⟨RawStep.par.subst0_par bodyStep argumentStep, contractumEq⟩

/-- Typed wrapper for non-dependent head-β SN expansion.

The reducibility-level lambda case needs SN of the redex
`app (lam body) argument` after the body IH proves SN of the
β-contractum.  Since typed SN is raw SN, this wrapper exposes the
raw `RawTerm.app_lam_isStronglyNormalizing` lemma at the `Term` layer. -/
theorem Term.app_lam_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {argumentRaw : RawTerm scope}
    {bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm)
    (contractumIsSN :
      Term.isStronglyNormalizing (Term.subst0 bodyTerm argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.app (Term.lam (codomainType := codomainType) bodyTerm)
        argumentTerm) :=
  RawTerm.app_lam_isStronglyNormalizing bodyIsSN argumentIsSN
    contractumIsSN

/-- Fundamental SN endpoint for `Term.lam` at `Ty.arrow`.

This packages the lambda value's SN conjunct after substitution.  The
premise is deliberately explicit: callers must still prove the body is
strongly normalizing under `termSubst.lift domainType`.  That is the
remaining load-bearing obligation for the substitution-parametric
`fundamental_lam` theorem. -/
theorem Reducible.fundamental_lam_at_arrow_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Term.lam_isStronglyNormalizing bodyIsSN

/-- Renaming-stable SN of `Term.lam` at `Ty.arrow` —
`IsRenamingStableIsSN` mirror of `fundamental_lam_at_arrow_sn`.

Same inline-rebuild as the dependent-Π variant: at each renamed
world we extend the renaming through the domain binder via
`TermRenaming.lift (domainType.subst sigma)` with `rho.lift`
injective per `RawRenaming.lift_injective`, project body SN at
the renamed world from the stable premise, then close with
`RawTerm.lam_isStronglyNormalizing` raw-indexed. -/
theorem Reducible.fundamental_lam_at_arrow_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyIsStable :
        IsRenamingStableIsSN
          (Ty.weaken_subst_commute sigma codomainType ▸
            Term.subst (termSubst.lift domainType) bodyTerm)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  intro _renamedScope _renamedCtx rho rhoIsInjective termRenaming
  have liftedInjective :=
    RawRenaming.lift_injective rho rhoIsInjective
  have liftedTermRenaming :=
    termRenaming.lift (domainType.subst sigma)
  have bodySNAtRho :=
    bodyIsStable liftedInjective liftedTermRenaming
  exact RawTerm.lam_isStronglyNormalizing bodySNAtRho

/-- Fundamental SN endpoint for the application closure of `Term.lam`
at `Ty.arrow`.

This isolates the SN part of the arrow closure after substitution:
once the lifted lambda body, the reducible argument, and the β
contractum are all SN, the substituted lambda application is SN.  The
remaining full `fundamental_lam` work is to produce the contractum
reducibility from the body IH and then lift SN to the codomain
`Reducible` witness. -/
theorem Reducible.fundamental_lam_at_arrow_app_sn
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
    (contractumIsSN :
      Term.isStronglyNormalizing
        (Term.subst0
          (Ty.weaken_subst_commute sigma codomainType ▸
            Term.subst (termSubst.lift domainType) bodyTerm)
          argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.app
        (Term.subst termSubst
          (Term.lam (codomainType := codomainType) bodyTerm))
        argumentTerm) :=
  Term.app_lam_isStronglyNormalizing bodyIsSN
    (Reducible.isStronglyNormalizing argumentReducible)
    contractumIsSN

/-- Renaming-stable head-β SN of `Term.app (Term.lam body) argument` at
`Ty.arrow` — `IsRenamingStableIsSN` mirror of
`fundamental_lam_at_arrow_app_sn`.

At each renamed world the body SN, argument SN (via Reducible), and
contractum SN witnesses are projected from the three stable premises,
then fed to the raw head-β combinator
`RawTerm.app_lam_isStronglyNormalizing`.  The contractum's raw form at
the renamed world is `((body.subst σ.lift).subst0 argument).rename ρ`;
the combinator wants
`((body.subst σ.lift).rename ρ.lift).subst0 (argument.rename ρ)`.
`RawTerm.subst0_rename_commute` aligns the two. -/
theorem Reducible.fundamental_lam_at_arrow_app_sn_stable
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
    (contractumIsStable :
        IsRenamingStableIsSN
          (Term.subst0
            (Ty.weaken_subst_commute sigma codomainType ▸
              Term.subst (termSubst.lift domainType) bodyTerm)
            argumentTerm)) :
    IsRenamingStableIsSN
      (Term.app
        (Term.subst termSubst
          (Term.lam (codomainType := codomainType) bodyTerm))
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

/-- Reducibility endpoint for a lambda whose codomain reducibility is
recoverable from strong normalization.

This isolates the solved part of the `fundamental_lam` blocker.  The
lambda value SN and head-beta application SN are already available from
the body SN plus the beta-contractum witness.  To upgrade the
application result from SN to `Reducible codomainType`, the caller must
provide the codomain-specific SN-to-Reducible bridge.  Closed/SN-fallback
codomains can supply that bridge directly; full compound codomains still
need their own head-beta/full-reducibility work. -/
theorem Reducible.lam_at_arrow_of_sn_codomain
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm scope}
        (resultTerm : Term context codomainType resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible codomainType resultTerm)
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm)
    (bodyContractumReducible :
      ∀ {argumentRaw : RawTerm scope}
        (argumentTerm : Term context domainType argumentRaw),
        Reducible domainType argumentTerm →
        Reducible (codomainType.weaken.subst0 domainType argumentRaw)
          (Term.subst0 bodyTerm argumentTerm)) :
    Reducible (Ty.arrow domainType codomainType)
      (Term.lam (codomainType := codomainType) bodyTerm) := by
  refine ⟨Term.lam_isStronglyNormalizing bodyIsSN, ?_⟩
  intro argumentTerm argumentReducible argumentIsReducible
  apply codomainReducibleOfSN
  exact Term.app_lam_isStronglyNormalizing bodyIsSN
    (Reducible.isStronglyNormalizing argumentIsReducible)
    (Reducible.isStronglyNormalizing
      (bodyContractumReducible argumentReducible argumentIsReducible))

/-- Substitution-parametric lambda reducibility when the codomain is
recoverable from strong normalization.

This is the current honest frontier for the full `fundamental_lam`
case.  It packages the arrow candidate proof once callers supply:

* reducibility of the substituted body under `termSubst.lift`;
* reducibility of every β contractum; and
* a codomain-specific bridge from SN back to `Reducible`.

Closed and SN-fallback codomains can provide the last bridge directly.
Compound codomains still need their own head-β/full-reducibility
transport; this theorem keeps that obligation explicit in the type. -/
theorem Reducible.fundamental_lam_at_arrow_of_sn_codomain
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
    (bodyContractumReducible :
      ∀ {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw),
        Reducible (domainType.subst sigma) argumentTerm →
        Reducible
          ((codomainType.subst sigma).weaken.subst0
            (domainType.subst sigma) argumentRaw)
          (Term.subst0
            (Ty.weaken_subst_commute sigma codomainType ▸
              Term.subst (termSubst.lift domainType) bodyTerm)
            argumentTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  change Reducible
    (Ty.arrow (domainType.subst sigma) (codomainType.subst sigma))
    (Term.lam
      (codomainType := codomainType.subst sigma)
      (Ty.weaken_subst_commute sigma codomainType ▸
        Term.subst (termSubst.lift domainType) bodyTerm))
  exact Reducible.lam_at_arrow_of_sn_codomain codomainReducibleOfSN
    (Reducible.isStronglyNormalizing bodyLiftReducible)
    bodyContractumReducible


end LeanFX2
