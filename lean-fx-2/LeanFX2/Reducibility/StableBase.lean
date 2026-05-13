import LeanFX2.Reducibility.Foundation

/-! # LeanFX2.Reducibility.StableBase — K12.20.U4 stable fundamental base

The "stable" cases of the fundamental lemma: type-preserving
wrappers (`subsume`, `modIntro`, `modElim`) where the current
`Reducible` arm reduces to plain `Term.isStronglyNormalizing`
(SN-direct, per `Reducibility.Classifier`).

The cascade is parametric over the wrapper's outer-mode/level
configuration but uniform in its proof structure: every SN-direct
arm shares the `Reducible.of_isStronglyNormalizing_when_SNDirect`
recovery, so the wrapper's `Term.isStronglyNormalizing` witness
lifts directly to `Reducible` at the wrapped Ty.

## What ships (~1.5K LoC)

* SN-direct fundamental cases for each closed-type variant of
  `subsume` / `modIntro` / `modElim` at every admitting Ty
  (unit / bool / nat / empty / interval / universe / session /
  effect / modal).
* Container-intro stable cases (listNil, optionNone, etc.).
* Stable modal wrappers (representatives + remaining cases).
* Stable universe fundamentals.
* Stable session / effect / interval fundamentals.
* K12.20.U4 stable subst rename output + forward rename cast HEq.

These are the propext-leak family flagged by `GatesNsSweepAxiom`
under the pre-2026-05-13 `IsSNDirect` wildcard form; with the
full-enum classifier they elaborate clean.

## Root status

Layer 3 metatheory leaf.  Consumed by `Reducibility.Fundamental*`
modules for the modal / cumulUp / subsume cases. -/

namespace LeanFX2


/-! ## K12.20.U4 stable fundamental base cases

The lambda route now consumes renaming-stable substitutions to build
`ReducibleSubst.lift`.  The eventual fundamental induction therefore
needs stable counterparts for the base cases, not only reducibility
endpoints.  Closed canonical introducers are stable directly: every
typed injective renaming of their substituted form is the same
canonical raw term, and the corresponding candidate is the base SN
clause. -/

/-- Unit fundamental result is stable under future-world renamings. -/
theorem Reducible.fundamental_unit_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.unit : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.unit (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.unit_isStronglyNormalizing

/-- Boolean true fundamental result is stable under future-world
renamings. -/
theorem Reducible.fundamental_boolTrue_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.boolTrue (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.boolTrue_isStronglyNormalizing

/-- Boolean false fundamental result is stable under future-world
renamings. -/
theorem Reducible.fundamental_boolFalse_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.boolFalse (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.boolFalse_isStronglyNormalizing

/-- Natural zero fundamental result is stable under future-world
renamings. -/
theorem Reducible.fundamental_natZero_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma} :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.natZero (context := sourceCtx))) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.natZero_isStronglyNormalizing

/-- **K12.20.U3.monotone SN-fallback arm**: unit reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.unit : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.unit : Ty level scope) sourceTerm) :
    Reducible ((Ty.unit : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: bool reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.bool : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.bool : Ty level scope) sourceTerm) :
    Reducible ((Ty.bool : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: nat reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.nat : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.nat : Ty level scope) sourceTerm) :
    Reducible ((Ty.nat : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: empty reducibility is stable
under one-binder weakening. -/
theorem Reducible.weaken_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.empty : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.empty : Ty level scope) sourceTerm) :
    Reducible ((Ty.empty : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: interval reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.interval : Ty level scope) sourceRaw}
    (sourceReducible : Reducible (Ty.interval : Ty level scope) sourceTerm) :
    Reducible ((Ty.interval : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: universe-code
reducibility is stable under one-binder weakening. -/
theorem Reducible.weaken_universe
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {sourceRaw : RawTerm scope}
    {sourceTerm :
      Term context (Ty.universe universeLevel levelLe : Ty level scope)
        sourceRaw}
    (sourceReducible :
      Reducible (Ty.universe universeLevel levelLe : Ty level scope)
        sourceTerm) :
    Reducible
      ((Ty.universe universeLevel levelLe : Ty level scope).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: type-variable fallback
reducibility is stable under one-binder weakening. -/
theorem Reducible.weaken_tyVar
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {position : Fin scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.tyVar position) sourceRaw}
    (sourceReducible : Reducible (Ty.tyVar position) sourceTerm) :
    Reducible ((Ty.tyVar position).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: session reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_session
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {protocolStep sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.session protocolStep) sourceRaw}
    (sourceReducible : Reducible (Ty.session protocolStep) sourceTerm) :
    Reducible ((Ty.session protocolStep).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: effect reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_effect
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {effectTag sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.effect carrierType effectTag) sourceRaw}
    (sourceReducible : Reducible (Ty.effect carrierType effectTag) sourceTerm) :
    Reducible ((Ty.effect carrierType effectTag).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

/-- **K12.20.U3.monotone SN-fallback arm**: modal reducibility is
stable under one-binder weakening. -/
theorem Reducible.weaken_modal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType carrierType : Ty level scope}
    {modalityTag : Nat}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context (Ty.modal modalityTag carrierType) sourceRaw}
    (sourceReducible :
      Reducible (Ty.modal modalityTag carrierType) sourceTerm) :
    Reducible ((Ty.modal modalityTag carrierType).weaken)
      (Term.weaken newType sourceTerm) :=
  Term.isStronglyNormalizing_weaken sourceReducible

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

/-- **K12.24.U5 path β SN expansion**.

If the path body, interval argument, and β-contractum are all strongly
normalizing, then the cubical redex `pathApp (pathLam body) interval`
is strongly normalizing.  This mirrors `app_lam_isStronglyNormalizing`:
congruence reducts recurse through the body/interval SN witnesses, while
the β arm is closed by CR2 from the contractum along `subst0_par`. -/
theorem RawTerm.pathApp_pathLam_isStronglyNormalizing {scope : Nat}
    {body : RawTerm (scope + 1)}
    (bodyIsSN : RawTerm.isStronglyNormalizing body) :
    ∀ {interval : RawTerm scope},
      RawTerm.isStronglyNormalizing interval →
      RawTerm.isStronglyNormalizing (body.subst0 interval) →
      RawTerm.isStronglyNormalizing
        (RawTerm.pathApp (RawTerm.pathLam body) interval) := by
  induction bodyIsSN with
  | intro currentBody bodyClosure bodyIH =>
    intro interval intervalIsSN betaContractumIsSN
    induction intervalIsSN with
    | intro currentInterval intervalClosure intervalIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.pathApp (RawTerm.pathLam currentBody) currentInterval) ?_
      intro target progressStep
      rcases RawStep.par.pathApp_inv progressStep.1 with
        ⟨pathTarget, intervalTarget, targetEq,
          pathStep, intervalStep⟩
        | ⟨bodyTarget, intervalTarget, targetEq,
            pathStep, intervalStep⟩
      · obtain ⟨bodyTarget, pathTargetEq, bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        subst pathTargetEq
        subst targetEq
        by_cases bodyEq : currentBody = bodyTarget
        · subst bodyEq
          by_cases intervalEq : currentInterval = intervalTarget
          · subst intervalEq
            exact False.elim (progressStep.2 rfl)
          · have intervalContractumIsSN :
                RawTerm.isStronglyNormalizing
                  (currentBody.subst0 intervalTarget) := by
              by_cases contractumEq :
                  currentBody.subst0 currentInterval =
                    currentBody.subst0 intervalTarget
              · rw [← contractumEq]
                exact betaContractumIsSN
              · exact RawTerm.isStronglyNormalizing.step_preserves
                  betaContractumIsSN
                  ⟨RawStep.par.subst0_par (RawStep.par.refl currentBody)
                    intervalStep, contractumEq⟩
            exact intervalIH intervalTarget ⟨intervalStep, intervalEq⟩
              intervalContractumIsSN
        · have bodyProgress :
              RawStep.parProgress currentBody bodyTarget :=
            ⟨bodyStep, bodyEq⟩
          have intervalTargetIsSN :
              RawTerm.isStronglyNormalizing intervalTarget := by
            by_cases intervalEq : currentInterval = intervalTarget
            · subst intervalEq
              exact RawTerm.isStronglyNormalizing.intro
                currentInterval intervalClosure
            · exact intervalClosure intervalTarget
                ⟨intervalStep, intervalEq⟩
          have bodyTargetContractumIsSN :
              RawTerm.isStronglyNormalizing
                (bodyTarget.subst0 intervalTarget) := by
            by_cases contractumEq :
                currentBody.subst0 currentInterval =
                  bodyTarget.subst0 intervalTarget
            · rw [← contractumEq]
              exact betaContractumIsSN
            · exact RawTerm.isStronglyNormalizing.step_preserves
                betaContractumIsSN
                ⟨RawStep.par.subst0_par bodyStep intervalStep,
                  contractumEq⟩
          exact bodyIH bodyTarget bodyProgress intervalTargetIsSN
            bodyTargetContractumIsSN
      · obtain ⟨bodyTargetFromPath, pathTargetEq, bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        cases pathTargetEq
        subst targetEq
        by_cases contractumEq :
            currentBody.subst0 currentInterval =
              bodyTarget.subst0 intervalTarget
        · rw [← contractumEq]
          exact betaContractumIsSN
        · exact RawTerm.isStronglyNormalizing.step_preserves
            betaContractumIsSN
            ⟨RawStep.par.subst0_par bodyStep intervalStep, contractumEq⟩

/-- Typed wrapper for cubical path β SN expansion.

The theorem only exposes the SN bridge for
`pathApp (pathLam body) interval`; Reducible-level backward closure at
the carrier type remains a separate head-β/CR3 problem. -/
theorem Term.pathApp_pathLam_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {intervalRaw : RawTerm scope}
    {bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    {intervalTerm : Term context Ty.interval intervalRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm)
    (intervalIsSN : Term.isStronglyNormalizing intervalTerm)
    (contractumIsSN :
      Term.isStronglyNormalizing (Term.subst0 bodyTerm intervalTerm)) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent
        (Term.pathLam modeIsUnivalent carrierType
          leftEndpoint rightEndpoint bodyTerm)
        intervalTerm) :=
  RawTerm.pathApp_pathLam_isStronglyNormalizing bodyIsSN intervalIsSN
    contractumIsSN

/-- **K12.24.U5 constant transport beta SN expansion**.

Transport across a syntactically constant path is strongly normalizing
whenever the transported value is.  Congruence on the constant path body
recurses through `RawStep.par.weaken_inv`; beta branches return a reduct
of the transported source.  The unrelated `uaToEquiv` and `pathCompose`
transport rules are impossible from a `pathLam _` head. -/
theorem RawTerm.transp_pathLam_weaken_isStronglyNormalizing {scope : Nat}
    {typeRaw : RawTerm scope}
    (typeIsSN : RawTerm.isStronglyNormalizing typeRaw) :
    ∀ {sourceRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing sourceRaw →
      RawTerm.isStronglyNormalizing
        (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRaw) := by
  induction typeIsSN with
  | intro currentType typeClosure typeIH =>
    intro sourceRaw sourceIsSN
    induction sourceIsSN with
    | intro currentSource sourceClosure sourceIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.transp (RawTerm.pathLam currentType.weaken)
          currentSource) ?_
      intro target progressStep
      rcases RawStep.par.transp_inv progressStep.1 with
        ⟨pathTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨typeRawSource, sourceTarget, pathEq, targetEq, sourceStep⟩
        | ⟨typeRawTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨proofRawSource, proofRawTarget, sourceTarget,
            pathEq, targetEq, _proofStep, _sourceStep⟩
        | ⟨proofRawTarget, sourceTarget, targetEq, pathStep, _sourceStep⟩
        | ⟨leftRawSource, leftRawTarget, rightRawSource, rightRawTarget,
            sourceTarget, pathEq, targetEq, _leftStep, _rightStep,
            _sourceStep⟩
        | ⟨leftRawTarget, rightRawTarget, sourceTarget, targetEq,
            pathStep, _sourceStep⟩
      · obtain ⟨bodyTarget, pathTargetEq, bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        subst pathTargetEq
        subst targetEq
        obtain ⟨typeTarget, bodyTargetEq⟩ :=
          RawStep.par.weaken_inv bodyStep
        subst bodyTargetEq
        have typeStep : RawStep.par currentType typeTarget := by
          have singletonStep :
              RawStep.par
                (currentType.weaken.subst
                  (RawTermSubst.singleton RawTerm.unit))
                (typeTarget.weaken.subst
                  (RawTermSubst.singleton RawTerm.unit)) :=
            RawStep.par.subst_par
              (fun _position => RawStep.par.refl _) bodyStep
          rw [RawTerm.weaken_subst_singleton currentType RawTerm.unit,
              RawTerm.weaken_subst_singleton typeTarget RawTerm.unit]
            at singletonStep
          exact singletonStep
        by_cases typeEq : currentType = typeTarget
        · subst typeEq
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact False.elim (progressStep.2 rfl)
          · exact sourceIH sourceTarget ⟨sourceStep, sourceEq⟩
        · have sourceTargetIsSN :
              RawTerm.isStronglyNormalizing sourceTarget := by
            by_cases sourceEq : currentSource = sourceTarget
            · subst sourceEq
              exact RawTerm.isStronglyNormalizing.intro
                currentSource sourceClosure
            · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
          exact typeIH typeTarget ⟨typeStep, typeEq⟩ sourceTargetIsSN
      · rw [targetEq]
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      · rw [targetEq]
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      · cases pathEq
      · obtain ⟨bodyTarget, pathTargetEq, _bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        cases pathTargetEq
      · cases pathEq
      · obtain ⟨bodyTarget, pathTargetEq, _bodyStep⟩ :=
          RawStep.par.pathLam_inv pathStep
        cases pathTargetEq

/-- Typed wrapper for constant cubical-transport beta SN expansion.

This packages the raw fact for the typed redex
`transp (pathLam typeCode.weaken) sourceValue`.  It is an SN bridge
only: no full transport Reducible endpoint is claimed here. -/
theorem Term.transp_pathLam_weaken_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {sourceType : Ty level scope}
    {typeRaw sourceRaw : RawTerm scope}
    {typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (typeCodeIsSN : Term.isStronglyNormalizing typeCode)
    (sourceIsSN : Term.isStronglyNormalizing sourceValue) :
    Term.isStronglyNormalizing
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType sourceType typeRaw typeRaw
        (Term.pathLam modeIsUnivalent
          (Ty.universe universeLevel universeLevelLt) typeRaw typeRaw
          (Term.weaken Ty.interval typeCode))
        sourceValue) :=
  RawTerm.transp_pathLam_weaken_isStronglyNormalizing typeCodeIsSN
    sourceIsSN

/-- General raw transport SN bridge with explicit non-congruence obligations.

`transp` is not a congruence-only constructor: `transp_inv` has direct
and deep beta arms for constant paths, univalence paths, and composed
paths.  The constant-path arms reduce to a reduct of the source term,
which follows from `sourceIsSN`.  The univalence and compose contracta
are not derivable from child SN alone here, so callers must provide the
two explicit contractum-SN closures. -/
theorem RawTerm.transp_isStronglyNormalizing {scope : Nat}
    {pathRaw : RawTerm scope}
    (pathIsSN : RawTerm.isStronglyNormalizing pathRaw) :
    ∀ {sourceRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing sourceRaw →
      (∀ {currentPath currentSource proofTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath (RawTerm.uaToEquiv proofTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.equivApply (RawTerm.uaToEquiv proofTarget)
            sourceTarget)) →
      (∀ {currentPath currentSource leftTarget rightTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath
          (RawTerm.pathCompose leftTarget rightTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.transp rightTarget
            (RawTerm.transp leftTarget sourceTarget))) →
      RawTerm.isStronglyNormalizing (RawTerm.transp pathRaw sourceRaw) := by
  induction pathIsSN with
  | intro currentPath pathClosure pathIH =>
    intro sourceRaw sourceIsSN uaContractumIsSN composeContractumIsSN
    induction sourceIsSN with
    | intro currentSource sourceClosure sourceIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.transp currentPath currentSource) ?_
      intro target progressStep
      let sourceTargetIsSN
          {sourceTarget : RawTerm scope}
          (sourceStep : RawStep.par currentSource sourceTarget) :
          RawTerm.isStronglyNormalizing sourceTarget := by
        by_cases sourceEq : currentSource = sourceTarget
        · subst sourceEq
          exact RawTerm.isStronglyNormalizing.intro
            currentSource sourceClosure
        · exact sourceClosure sourceTarget ⟨sourceStep, sourceEq⟩
      rcases RawStep.par.transp_inv progressStep.1 with
        ⟨pathTarget, sourceTarget, targetEq, pathStep, sourceStep⟩
        | ⟨_typeRawSource, sourceTarget, _pathEq,
            targetEq, sourceStep⟩
        | ⟨_typeRawTarget, sourceTarget, targetEq,
            _pathStep, sourceStep⟩
        | ⟨_proofRawSource, proofRawTarget, sourceTarget,
            pathEq, targetEq, proofStep, sourceStep⟩
        | ⟨proofRawTarget, sourceTarget, targetEq,
            pathStep, sourceStep⟩
        | ⟨leftRawSource, leftRawTarget, rightRawSource,
            rightRawTarget, sourceTarget, pathEq, targetEq,
            leftStep, rightStep, sourceStep⟩
        | ⟨leftRawTarget, rightRawTarget, sourceTarget,
            targetEq, pathStep, sourceStep⟩
      · subst targetEq
        by_cases pathEq : currentPath = pathTarget
        · subst pathEq
          by_cases sourceEq : currentSource = sourceTarget
          · subst sourceEq
            exact False.elim (progressStep.2 rfl)
          · exact sourceIH sourceTarget ⟨sourceStep, sourceEq⟩
        · exact pathIH pathTarget ⟨pathStep, pathEq⟩
            (sourceTargetIsSN sourceStep)
            uaContractumIsSN composeContractumIsSN
      · rw [targetEq]
        exact sourceTargetIsSN sourceStep
      · rw [targetEq]
        exact sourceTargetIsSN sourceStep
      · subst targetEq
        subst pathEq
        exact uaContractumIsSN
          (RawStep.par.uaToEquivCong proofStep) sourceStep
      · rw [targetEq]
        exact uaContractumIsSN pathStep sourceStep
      · subst targetEq
        subst pathEq
        exact composeContractumIsSN
          (RawStep.par.pathComposeCong leftStep rightStep) sourceStep
      · rw [targetEq]
        exact composeContractumIsSN pathStep sourceStep

/-- Typed transport SN endpoint with the raw beta-contractum obligations
kept visible.

This is the honest surface endpoint for `Term.transp`: child SN proves
the congruence and constant-path beta branches, while univalence and
path-composition beta branches are explicit premises until their typed
contractum closures are integrated into the relevant reducibility cases. -/
theorem Term.transp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    {typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (pathIsSN : Term.isStronglyNormalizing typePath)
    (sourceIsSN : Term.isStronglyNormalizing sourceValue)
    (uaContractumIsSN :
      ∀ {currentPath currentSource proofTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath (RawTerm.uaToEquiv proofTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.equivApply (RawTerm.uaToEquiv proofTarget)
            sourceTarget))
    (composeContractumIsSN :
      ∀ {currentPath currentSource leftTarget rightTarget sourceTarget :
            RawTerm scope},
        RawStep.par currentPath
          (RawTerm.pathCompose leftTarget rightTarget) →
        RawStep.par currentSource sourceTarget →
        RawTerm.isStronglyNormalizing
          (RawTerm.transp rightTarget
            (RawTerm.transp leftTarget sourceTarget))) :
    Term.isStronglyNormalizing
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) :=
  RawTerm.transp_isStronglyNormalizing pathIsSN sourceIsSN
    uaContractumIsSN composeContractumIsSN

/-- **K12.24 hcomp SN preservation**.

The current raw `hcomp` operator has congruence only: all progress
steps are pointwise steps in the sides and cap payloads.  Therefore SN
of both payloads gives SN of the `hcomp` term by the same nested
induction pattern as binary constructors.  This is not a boundary
computation rule and does not claim full Reducible output at an
arbitrary carrier. -/
theorem RawTerm.hcomp_isStronglyNormalizing {scope : Nat}
    {sidesRaw : RawTerm scope}
    (sidesIsSN : RawTerm.isStronglyNormalizing sidesRaw) :
    ∀ {capRaw : RawTerm scope},
      RawTerm.isStronglyNormalizing capRaw →
      RawTerm.isStronglyNormalizing (RawTerm.hcomp sidesRaw capRaw) := by
  induction sidesIsSN with
  | intro currentSides sidesClosure sidesIH =>
    intro capRaw capIsSN
    induction capIsSN with
    | intro currentCap capClosure capIH =>
      refine RawTerm.isStronglyNormalizing.intro
        (RawTerm.hcomp currentSides currentCap) ?_
      intro target progressStep
      obtain ⟨sidesTarget, capTarget, targetEq, sidesStep, capStep⟩ :=
        RawStep.par.hcomp_inv progressStep.1
      subst targetEq
      by_cases sidesEq : currentSides = sidesTarget
      · subst sidesEq
        by_cases capEq : currentCap = capTarget
        · subst capEq
          exact False.elim (progressStep.2 rfl)
        · exact capIH capTarget ⟨capStep, capEq⟩
      · have sidesProgress :
            RawStep.parProgress currentSides sidesTarget :=
          ⟨sidesStep, sidesEq⟩
        have capTargetIsSN : RawTerm.isStronglyNormalizing capTarget := by
          by_cases capEq : currentCap = capTarget
          · subst capEq
            exact RawTerm.isStronglyNormalizing.intro currentCap capClosure
          · exact capClosure capTarget ⟨capStep, capEq⟩
        exact sidesIH sidesTarget sidesProgress capTargetIsSN

/-- Typed wrapper for homogeneous-composition SN preservation.

This mirrors the raw congruence-only `hcomp` fragment.  It supplies the
SN bridge needed for cubical support work while keeping the Reducible
carrier closure separate. -/
theorem Term.hcomp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    {sidesValue : Term context carrierType sidesRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIsSN : Term.isStronglyNormalizing sidesValue)
    (capIsSN : Term.isStronglyNormalizing capValue) :
    Term.isStronglyNormalizing
      (Term.hcomp modeIsUnivalent sidesValue capValue) :=
  RawTerm.hcomp_isStronglyNormalizing sidesIsSN capIsSN

/-- Shape-specialized inversion for application SN.  The induction is
over an arbitrary SN source and receives the application shape as an
equality, which keeps Lean's indexed-inductive eliminator in the
structural fragment. -/
theorem RawTerm.app_function_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {functionRaw argumentRaw : RawTerm scope},
      source = RawTerm.app functionRaw argumentRaw →
      RawTerm.isStronglyNormalizing functionRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro functionRaw argumentRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro functionRaw ?_
    intro functionTarget functionProgress
    have appProgress :
        RawStep.parProgress
          (RawTerm.app functionRaw argumentRaw)
          (RawTerm.app functionTarget argumentRaw) := by
      refine ⟨RawStep.par.app functionProgress.1
        (RawStep.par.refl argumentRaw), ?_⟩
      intro appEq
      apply functionProgress.2
      injection appEq
    exact inductiveHypothesis
      (RawTerm.app functionTarget argumentRaw) appProgress rfl

/-- If an application is strongly normalizing, its function subterm is
strongly normalizing.  This is used by SN-output eliminator CR3: branch
closures often expose SN only after applying a branch, while neutral
eliminator congruence needs SN of the branch term itself. -/
theorem RawTerm.app_function_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app functionRaw argumentRaw)) :
    RawTerm.isStronglyNormalizing functionRaw :=
  RawTerm.app_function_isStronglyNormalizing_aux appIsSN rfl

/-- Shape-specialized inversion for application-argument SN.  This is
the argument-position sibling of `app_function_isStronglyNormalizing_aux`:
the induction is over an arbitrary SN source and receives the application
shape as an equality. -/
theorem RawTerm.app_argument_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {functionRaw argumentRaw : RawTerm scope},
      source = RawTerm.app functionRaw argumentRaw →
      RawTerm.isStronglyNormalizing argumentRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro functionRaw argumentRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro argumentRaw ?_
    intro argumentTarget argumentProgress
    have appProgress :
        RawStep.parProgress
          (RawTerm.app functionRaw argumentRaw)
          (RawTerm.app functionRaw argumentTarget) := by
      refine ⟨RawStep.par.app (RawStep.par.refl functionRaw)
        argumentProgress.1, ?_⟩
      intro appEq
      apply argumentProgress.2
      injection appEq
    exact inductiveHypothesis
      (RawTerm.app functionRaw argumentTarget) appProgress rfl

/-- If an application is strongly normalizing, its argument subterm is
strongly normalizing.  Used alongside function-position inversion when
head-β and eliminator proofs need to recover SN of raw subterms from an
already-normalizing application. -/
theorem RawTerm.app_argument_isStronglyNormalizing {scope : Nat}
    {functionRaw argumentRaw : RawTerm scope}
    (appIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.app functionRaw argumentRaw)) :
    RawTerm.isStronglyNormalizing argumentRaw :=
  RawTerm.app_argument_isStronglyNormalizing_aux appIsSN rfl

/-- Shape-specialized inversion for predecessor SN from successor SN. -/
theorem RawTerm.natSucc_predecessor_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {predecessorRaw : RawTerm scope},
      source = RawTerm.natSucc predecessorRaw →
      RawTerm.isStronglyNormalizing predecessorRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro predecessorRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro predecessorRaw ?_
    intro predecessorTarget predecessorProgress
    have succProgress :
        RawStep.parProgress
          (RawTerm.natSucc predecessorRaw)
          (RawTerm.natSucc predecessorTarget) := by
      refine ⟨RawStep.par.natSucc predecessorProgress.1, ?_⟩
      intro succEq
      apply predecessorProgress.2
      injection succEq
    exact inductiveHypothesis
      (RawTerm.natSucc predecessorTarget) succProgress rfl

/-- If a natural successor is strongly normalizing, its predecessor is
strongly normalizing.  Used by nat-eliminator successor ι expansions. -/
theorem RawTerm.natSucc_predecessor_isStronglyNormalizing {scope : Nat}
    {predecessorRaw : RawTerm scope}
    (successorIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.natSucc predecessorRaw)) :
    RawTerm.isStronglyNormalizing predecessorRaw :=
  RawTerm.natSucc_predecessor_isStronglyNormalizing_aux
    successorIsSN rfl

/-- Shape-specialized inversion for first component SN from pair SN. -/
theorem RawTerm.pair_first_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {firstRaw secondRaw : RawTerm scope},
      source = RawTerm.pair firstRaw secondRaw →
      RawTerm.isStronglyNormalizing firstRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro firstRaw secondRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro firstRaw ?_
    intro firstTarget firstProgress
    have pairProgress :
        RawStep.parProgress
          (RawTerm.pair firstRaw secondRaw)
          (RawTerm.pair firstTarget secondRaw) := by
      refine ⟨RawStep.par.pair firstProgress.1
        (RawStep.par.refl secondRaw), ?_⟩
      intro pairEq
      apply firstProgress.2
      injection pairEq
    exact inductiveHypothesis
      (RawTerm.pair firstTarget secondRaw) pairProgress rfl

/-- If a pair is strongly normalizing, its first component is strongly
normalizing. -/
theorem RawTerm.pair_first_isStronglyNormalizing {scope : Nat}
    {firstRaw secondRaw : RawTerm scope}
    (pairIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstRaw secondRaw)) :
    RawTerm.isStronglyNormalizing firstRaw :=
  RawTerm.pair_first_isStronglyNormalizing_aux pairIsSN rfl

/-- Shape-specialized inversion for second component SN from pair SN. -/
theorem RawTerm.pair_second_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {firstRaw secondRaw : RawTerm scope},
      source = RawTerm.pair firstRaw secondRaw →
      RawTerm.isStronglyNormalizing secondRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro firstRaw secondRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro secondRaw ?_
    intro secondTarget secondProgress
    have pairProgress :
        RawStep.parProgress
          (RawTerm.pair firstRaw secondRaw)
          (RawTerm.pair firstRaw secondTarget) := by
      refine ⟨RawStep.par.pair (RawStep.par.refl firstRaw)
        secondProgress.1, ?_⟩
      intro pairEq
      apply secondProgress.2
      injection pairEq
    exact inductiveHypothesis
      (RawTerm.pair firstRaw secondTarget) pairProgress rfl

/-- If a pair is strongly normalizing, its second component is strongly
normalizing. -/
theorem RawTerm.pair_second_isStronglyNormalizing {scope : Nat}
    {firstRaw secondRaw : RawTerm scope}
    (pairIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.pair firstRaw secondRaw)) :
    RawTerm.isStronglyNormalizing secondRaw :=
  RawTerm.pair_second_isStronglyNormalizing_aux pairIsSN rfl

/-- Shape-specialized inversion for option payload SN. -/
theorem RawTerm.optionSome_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.optionSome valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have optionProgress :
        RawStep.parProgress
          (RawTerm.optionSome valueRaw)
          (RawTerm.optionSome valueTarget) := by
      refine ⟨RawStep.par.optionSome valueProgress.1, ?_⟩
      intro optionEq
      apply valueProgress.2
      injection optionEq
    exact inductiveHypothesis
      (RawTerm.optionSome valueTarget) optionProgress rfl

/-- If `optionSome value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.optionSome_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (optionIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.optionSome valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.optionSome_value_isStronglyNormalizing_aux optionIsSN rfl

/-- Shape-specialized inversion for either-left payload SN. -/
theorem RawTerm.eitherInl_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.eitherInl valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have eitherProgress :
        RawStep.parProgress
          (RawTerm.eitherInl valueRaw)
          (RawTerm.eitherInl valueTarget) := by
      refine ⟨RawStep.par.eitherInl valueProgress.1, ?_⟩
      intro eitherEq
      apply valueProgress.2
      injection eitherEq
    exact inductiveHypothesis
      (RawTerm.eitherInl valueTarget) eitherProgress rfl

/-- If `eitherInl value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.eitherInl_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (eitherIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherInl valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.eitherInl_value_isStronglyNormalizing_aux eitherIsSN rfl

/-- Shape-specialized inversion for either-right payload SN. -/
theorem RawTerm.eitherInr_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw : RawTerm scope},
      source = RawTerm.eitherInr valueRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have eitherProgress :
        RawStep.parProgress
          (RawTerm.eitherInr valueRaw)
          (RawTerm.eitherInr valueTarget) := by
      refine ⟨RawStep.par.eitherInr valueProgress.1, ?_⟩
      intro eitherEq
      apply valueProgress.2
      injection eitherEq
    exact inductiveHypothesis
      (RawTerm.eitherInr valueTarget) eitherProgress rfl

/-- If `eitherInr value` is strongly normalizing, then `value` is
strongly normalizing. -/
theorem RawTerm.eitherInr_value_isStronglyNormalizing {scope : Nat}
    {valueRaw : RawTerm scope}
    (eitherIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.eitherInr valueRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.eitherInr_value_isStronglyNormalizing_aux eitherIsSN rfl

/-- Shape-specialized inversion for single-field record payload SN. -/
theorem RawTerm.recordIntro_field_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {fieldRaw : RawTerm scope},
      source = RawTerm.recordIntro fieldRaw →
      RawTerm.isStronglyNormalizing fieldRaw := by
  induction sourceIsSN with
  | intro currentSource _ inductiveHypothesis =>
    intro fieldRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro fieldRaw ?_
    intro fieldTarget fieldProgress
    have recordProgress :
        RawStep.parProgress
          (RawTerm.recordIntro fieldRaw)
          (RawTerm.recordIntro fieldTarget) := by
      refine ⟨RawStep.par.recordIntroCong fieldProgress.1, ?_⟩
      intro recordEq
      apply fieldProgress.2
      injection recordEq
    exact inductiveHypothesis
      (RawTerm.recordIntro fieldTarget) recordProgress rfl

/-- If a record introduction is strongly normalizing, then its field is
strongly normalizing. -/
theorem RawTerm.recordIntro_field_isStronglyNormalizing {scope : Nat}
    {fieldRaw : RawTerm scope}
    (recordIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.recordIntro fieldRaw)) :
    RawTerm.isStronglyNormalizing fieldRaw :=
  RawTerm.recordIntro_field_isStronglyNormalizing_aux recordIsSN rfl

/-- Shape-specialized inversion for refinement-intro value payload SN. -/
theorem RawTerm.refineIntro_value_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {valueRaw proofRaw : RawTerm scope},
      source = RawTerm.refineIntro valueRaw proofRaw →
      RawTerm.isStronglyNormalizing valueRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro valueRaw proofRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro valueRaw ?_
    intro valueTarget valueProgress
    have refineProgress :
        RawStep.parProgress
          (RawTerm.refineIntro valueRaw proofRaw)
          (RawTerm.refineIntro valueTarget proofRaw) := by
      refine ⟨RawStep.par.refineIntroCong valueProgress.1
        (RawStep.par.refl proofRaw), ?_⟩
      intro refineEq
      apply valueProgress.2
      injection refineEq
    exact inductiveHypothesis
      (RawTerm.refineIntro valueTarget proofRaw) refineProgress rfl

/-- If a refinement introduction is strongly normalizing, then its
value payload is strongly normalizing. -/
theorem RawTerm.refineIntro_value_isStronglyNormalizing {scope : Nat}
    {valueRaw proofRaw : RawTerm scope}
    (refineIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.refineIntro valueRaw proofRaw)) :
    RawTerm.isStronglyNormalizing valueRaw :=
  RawTerm.refineIntro_value_isStronglyNormalizing_aux refineIsSN rfl

/-- Shape-specialized inversion for Glue-intro base payload SN. -/
theorem RawTerm.glueIntro_base_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {baseRaw partialRaw : RawTerm scope},
      source = RawTerm.glueIntro baseRaw partialRaw →
      RawTerm.isStronglyNormalizing baseRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro baseRaw partialRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro baseRaw ?_
    intro baseTarget baseProgress
    have glueProgress :
        RawStep.parProgress
          (RawTerm.glueIntro baseRaw partialRaw)
          (RawTerm.glueIntro baseTarget partialRaw) := by
      refine ⟨RawStep.par.glueIntroCong baseProgress.1
        (RawStep.par.refl partialRaw), ?_⟩
      intro glueEq
      apply baseProgress.2
      injection glueEq
    exact inductiveHypothesis
      (RawTerm.glueIntro baseTarget partialRaw) glueProgress rfl

/-- If a Glue introduction is strongly normalizing, then its base
payload is strongly normalizing. -/
theorem RawTerm.glueIntro_base_isStronglyNormalizing {scope : Nat}
    {baseRaw partialRaw : RawTerm scope}
    (glueIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.glueIntro baseRaw partialRaw)) :
    RawTerm.isStronglyNormalizing baseRaw :=
  RawTerm.glueIntro_base_isStronglyNormalizing_aux glueIsSN rfl

/-- Shape-specialized inversion for list-cons head SN. -/
theorem RawTerm.listCons_head_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {headRaw tailRaw : RawTerm scope},
      source = RawTerm.listCons headRaw tailRaw →
      RawTerm.isStronglyNormalizing headRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro headRaw tailRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro headRaw ?_
    intro headTarget headProgress
    have consProgress :
        RawStep.parProgress
          (RawTerm.listCons headRaw tailRaw)
          (RawTerm.listCons headTarget tailRaw) := by
      refine ⟨RawStep.par.listCons headProgress.1
        (RawStep.par.refl tailRaw), ?_⟩
      intro consEq
      apply headProgress.2
      injection consEq
    exact inductiveHypothesis
      (RawTerm.listCons headTarget tailRaw) consProgress rfl

/-- If `listCons head tail` is strongly normalizing, then `head` is
strongly normalizing. -/
theorem RawTerm.listCons_head_isStronglyNormalizing {scope : Nat}
    {headRaw tailRaw : RawTerm scope}
    (consIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headRaw tailRaw)) :
    RawTerm.isStronglyNormalizing headRaw :=
  RawTerm.listCons_head_isStronglyNormalizing_aux consIsSN rfl

/-- Shape-specialized inversion for list-cons tail SN. -/
theorem RawTerm.listCons_tail_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {headRaw tailRaw : RawTerm scope},
      source = RawTerm.listCons headRaw tailRaw →
      RawTerm.isStronglyNormalizing tailRaw := by
  induction sourceIsSN with
  | intro currentSource closure inductiveHypothesis =>
    intro headRaw tailRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro tailRaw ?_
    intro tailTarget tailProgress
    have consProgress :
        RawStep.parProgress
          (RawTerm.listCons headRaw tailRaw)
          (RawTerm.listCons headRaw tailTarget) := by
      refine ⟨RawStep.par.listCons (RawStep.par.refl headRaw)
        tailProgress.1, ?_⟩
      intro consEq
      apply tailProgress.2
      injection consEq
    exact inductiveHypothesis
      (RawTerm.listCons headRaw tailTarget) consProgress rfl

/-- If `listCons head tail` is strongly normalizing, then `tail` is
strongly normalizing. -/
theorem RawTerm.listCons_tail_isStronglyNormalizing {scope : Nat}
    {headRaw tailRaw : RawTerm scope}
    (consIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.listCons headRaw tailRaw)) :
    RawTerm.isStronglyNormalizing tailRaw :=
  RawTerm.listCons_tail_isStronglyNormalizing_aux consIsSN rfl

/-- Shape-specialized inversion for modal-introduction payload SN. -/
theorem RawTerm.modIntro_inner_isStronglyNormalizing_aux {scope : Nat}
    {source : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source) :
    ∀ {innerRaw : RawTerm scope},
      source = RawTerm.modIntro innerRaw →
      RawTerm.isStronglyNormalizing innerRaw := by
  induction sourceIsSN with
  | intro currentSource _ inductiveHypothesis =>
    intro innerRaw sourceEq
    cases sourceEq
    refine RawTerm.isStronglyNormalizing.intro innerRaw ?_
    intro innerTarget innerProgress
    have introProgress :
        RawStep.parProgress
          (RawTerm.modIntro innerRaw)
          (RawTerm.modIntro innerTarget) := by
      refine ⟨RawStep.par.modIntro innerProgress.1, ?_⟩
      intro introEq
      apply innerProgress.2
      injection introEq
    exact inductiveHypothesis
      (RawTerm.modIntro innerTarget) introProgress rfl

/-- If `modIntro inner` is strongly normalizing, then `inner` is
strongly normalizing. -/
theorem RawTerm.modIntro_inner_isStronglyNormalizing {scope : Nat}
    {innerRaw : RawTerm scope}
    (introIsSN :
      RawTerm.isStronglyNormalizing (RawTerm.modIntro innerRaw)) :
    RawTerm.isStronglyNormalizing innerRaw :=
  RawTerm.modIntro_inner_isStronglyNormalizing_aux introIsSN rfl

/-- **K12.20.U2 raw CR3 skeleton**: a raw term is strongly
normalizing when every non-trivial parallel-progress reduct is
strongly normalizing.

This is the constructor direction of the SN definition, named because
the typed CR3 proof repeatedly reduces its SN-direct arms to exactly
this shape.  Neutrality is intentionally not required here: neutrality
is what makes the premise provable for variables and stuck eliminators;
the raw SN constructor itself only needs the reduct closure. -/
theorem RawTerm.isStronglyNormalizing.of_progress_closure {scope : Nat}
    {source : RawTerm scope}
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress source target →
        RawTerm.isStronglyNormalizing target) :
    RawTerm.isStronglyNormalizing source :=
  RawTerm.isStronglyNormalizing.intro source closure

/-- Typed wrapper around `RawTerm.isStronglyNormalizing.of_progress_closure`.
The term's type is irrelevant because typed SN is raw SN of the term's
structural raw index. -/
theorem Term.isStronglyNormalizing.of_raw_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Term.isStronglyNormalizing sourceTerm :=
  RawTerm.isStronglyNormalizing.of_progress_closure closure

/-- **K12.20.U2 raw CR3, neutral form**: a neutral raw term is SN
when all of its non-trivial progress reducts are SN.

The neutral witness is not computationally needed by the SN
constructor; it records the Tait CR3 contract at the call site.  In
later compound arms the neutral witness is what makes the reduct
closure available, while this lemma performs the final SN packaging. -/
theorem RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure
    {scope : Nat}
    {source : RawTerm scope}
    (_sourceIsNeutral : RawTerm.IsNeutral source)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress source target →
        RawTerm.isStronglyNormalizing target) :
    RawTerm.isStronglyNormalizing source :=
  RawTerm.isStronglyNormalizing.of_progress_closure closure

/-- Typed wrapper for the neutral raw CR3 form. -/
theorem Term.isStronglyNormalizing_of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (sourceIsNeutral : RawTerm.IsNeutral sourceRaw)
    (closure :
      ∀ target : RawTerm scope,
        RawStep.parProgress sourceRaw target →
        RawTerm.isStronglyNormalizing target) :
    Term.isStronglyNormalizing sourceTerm :=
  RawTerm.IsNeutral.isStronglyNormalizing_of_progress_closure
    sourceIsNeutral closure


end LeanFX2
