import LeanFX2.Reducibility.FundamentalEliminators

/-! # LeanFX2.Reducibility.FundamentalAliases.Aliases

Remaining SN-output endpoint aliases: short wrappers re-exposing
existing fundamental-theorem outputs as Term SN witnesses for
downstream consumption — `fundamental_*_at_*` projections
(sigmaTy / piTy / idJ / oeqJ / idStrictRec / refl / oeqRefl /
idStrictRefl) plus their `Term.identity_*_of_endpoint` Term
wrappers.

## Root status

Layer 3 metatheory leaf.  First slice of FundamentalAliases. -/

namespace LeanFX2


/-! ## Remaining SN-output endpoint aliases

These aliases complete the non-`_sn` naming pass for theorem statements
whose conclusion is intentionally the M04 endpoint: strong normalization.
The old names remain available for compatibility. -/

/-- Fundamental case: `Term.snd` at `Ty.sigmaTy`
(SN-output endpoint). -/
theorem Reducible.fundamental_snd_at_sigmaTy
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH :
        Reducible ((Ty.sigmaTy firstType secondType).subst sigma)
                  (Term.subst termSubst pairTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.snd pairTerm)) :=
  Reducible.fundamental_snd_at_sigmaTy_sn pairIH

/-- Renaming-stable alias of `fundamental_snd_at_sigmaTy`.  Forwards to
the matching `_sn_stable` companion. -/
theorem Reducible.fundamental_snd_at_sigmaTy_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm :
        Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsStable :
        IsRenamingStableReducible
          ((Ty.sigmaTy firstType secondType).subst sigma)
          (Term.subst termSubst pairTerm)) :
    IsRenamingStableIsSN
      (Term.subst termSubst (Term.snd pairTerm)) :=
  Reducible.fundamental_snd_at_sigmaTy_sn_stable pairIsStable

/-- Fundamental case: `Term.appPi` at `Ty.piTy`
(SN-output endpoint). -/
theorem Reducible.fundamental_appPi_at_piTy
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIH :
        Reducible ((Ty.piTy domainType codomainType).subst sigma)
                  (Term.subst termSubst functionTerm))
    (argumentIH :
        Reducible (domainType.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.appPi functionTerm argumentTerm)) :=
  Reducible.fundamental_appPi_at_piTy_sn functionIH argumentIH

/-- Renaming-stable alias of `fundamental_appPi_at_piTy`.  Forwards to
the matching `_sn_stable` companion. -/
theorem Reducible.fundamental_appPi_at_piTy_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIsStable :
        IsRenamingStableReducible
          ((Ty.piTy domainType codomainType).subst sigma)
          (Term.subst termSubst functionTerm))
    (argumentIsStable :
        IsRenamingStableReducible (domainType.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    IsRenamingStableIsSN
      (Term.subst termSubst (Term.appPi functionTerm argumentTerm)) :=
  Reducible.fundamental_appPi_at_piTy_sn_stable functionIsStable argumentIsStable

/-- **K12.27 identity-substitution application SN endpoint**.

This packages the application case needed by the identity-only M04 route:
if the function and argument are reducible after identity substitution,
then the original `Term.app` is strongly normalizing.  The theorem uses
the full arrow application endpoint at identity and then erases the
identity substitution from the raw index; it does not claim generic
substitution lifting or world weakening. -/
theorem Reducible.fundamental_identity_app_at_arrow_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIdentityReducible :
        Reducible ((Ty.arrow domainType codomainType).subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) functionTerm))
    (argumentIdentityReducible :
        Reducible (domainType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) argumentTerm)) :
    Term.isStronglyNormalizing (Term.app functionTerm argumentTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.app functionTerm argumentTerm)
    (Reducible.isStronglyNormalizing
      (Reducible.fundamental_app_at_arrow
        (termSubst := TermSubst.identity sourceCtx)
        functionIdentityReducible argumentIdentityReducible))

/-- **K12.27 identity-substitution dependent application SN endpoint**.

This is the `appPi` sibling of
`fundamental_identity_app_at_arrow_sn`.  The present `piTy` candidate
stores an SN-output application closure, so the proof applies that
endpoint at identity and erases identity substitution from the original
dependent application. -/
theorem Reducible.fundamental_identity_appPi_at_piTy_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
        Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionIdentityReducible :
        Reducible ((Ty.piTy domainType codomainType).subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) functionTerm))
    (argumentIdentityReducible :
        Reducible (domainType.subst Subst.identity)
          (Term.subst (TermSubst.identity sourceCtx) argumentTerm)) :
    Term.isStronglyNormalizing (Term.appPi functionTerm argumentTerm) :=
  Term.strong_normalization_of_identity_subst
    (Term.appPi functionTerm argumentTerm)
    (Reducible.fundamental_appPi_at_piTy
      (termSubst := TermSubst.identity sourceCtx)
      functionIdentityReducible argumentIdentityReducible)

/-- Fundamental case: `Term.idJ` at `Ty.id`
(SN-output endpoint). -/
theorem Reducible.fundamental_idJ_at_id
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.id carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.idJ baseCase witness)) :=
  Reducible.fundamental_idJ_at_id_sn baseIH witnessIH

/-- Renaming-stable alias of `fundamental_idJ_at_id`.  The plain form
above is a one-line wrapper of `_sn`; the renaming-stable mirror is the
matching one-line wrapper of `_sn_stable`. -/
theorem Reducible.fundamental_idJ_at_id_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIsStable :
        IsRenamingStableReducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIsStable :
        IsRenamingStableReducible
          ((Ty.id carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    IsRenamingStableIsSN
      (Term.subst termSubst (Term.idJ baseCase witness)) :=
  Reducible.fundamental_idJ_at_id_sn_stable baseIsStable witnessIsStable

/-- Fundamental case: `Term.oeqJ` at `Ty.oeq`
(SN-output endpoint). -/
theorem Reducible.fundamental_oeqJ_at_oeq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible ((Ty.oeq carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.oeqJ baseCase witness)) :=
  Reducible.fundamental_oeqJ_at_oeq_sn baseIH witnessIH

/-- Renaming-stable alias of `fundamental_oeqJ_at_oeq`.  Same shape as
the `_idJ` alias above. -/
theorem Reducible.fundamental_oeqJ_at_oeq_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIsStable :
        IsRenamingStableReducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIsStable :
        IsRenamingStableReducible
          ((Ty.oeq carrier leftEndpoint rightEndpoint).subst sigma)
                  (Term.subst termSubst witness)) :
    IsRenamingStableIsSN
      (Term.subst termSubst (Term.oeqJ baseCase witness)) :=
  Reducible.fundamental_oeqJ_at_oeq_sn_stable baseIsStable witnessIsStable

/-- Fundamental case: `Term.idStrictRec` at `Ty.idStrict`
(SN-output endpoint). -/
theorem Reducible.fundamental_idStrictRec_at_idStrict
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx
          (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH :
        Reducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIH :
        Reducible
          ((Ty.idStrict carrier leftEndpoint rightEndpoint).subst sigma)
          (Term.subst termSubst witness)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseCase witness)) :=
  Reducible.fundamental_idStrictRec_at_idStrict_sn
    modeIsStrict baseIH witnessIH

/-- Renaming-stable alias of `fundamental_idStrictRec_at_idStrict`.
Mode equality is world-invariant, so the stable mirror propagates it
unchanged into the underlying `_sn_stable` companion. -/
theorem Reducible.fundamental_idStrictRec_at_idStrict_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
        Term sourceCtx
          (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIsStable :
        IsRenamingStableReducible (motiveType.subst sigma)
                  (Term.subst termSubst baseCase))
    (witnessIsStable :
        IsRenamingStableReducible
          ((Ty.idStrict carrier leftEndpoint rightEndpoint).subst sigma)
          (Term.subst termSubst witness)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.idStrictRec modeIsStrict baseCase witness)) :=
  Reducible.fundamental_idStrictRec_at_idStrict_sn_stable
    modeIsStrict baseIsStable witnessIsStable

/-- Fundamental case: `Term.refl` at `Ty.id` with an explicit
endpoint SN premise. -/
theorem Reducible.fundamental_refl_at_id_of_endpoint
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.id carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.refl carrier rawWitness)) :=
  Reducible.fundamental_refl_at_id_of_endpoint_sn endpointIsSN

/-- Fundamental case: `Term.oeqRefl` at `Ty.oeq` with an explicit
endpoint SN premise. -/
theorem Reducible.fundamental_oeqRefl_at_oeq_of_endpoint
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.oeq carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst (Term.oeqRefl carrier rawWitness)) :=
  Reducible.fundamental_oeqRefl_at_oeq_of_endpoint_sn endpointIsSN

/-- Fundamental case: `Term.idStrictRefl` at `Ty.idStrict` with an
explicit endpoint SN premise. -/
theorem Reducible.fundamental_idStrictRefl_at_idStrict_of_endpoint
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN :
      RawTerm.isStronglyNormalizing (rawWitness.subst sigma.forRaw)) :
    Reducible
      ((Ty.idStrict carrier rawWitness rawWitness).subst sigma)
      (Term.subst termSubst
        (Term.idStrictRefl modeIsStrict carrier rawWitness)) :=
  Reducible.fundamental_idStrictRefl_at_idStrict_of_endpoint_sn
    modeIsStrict endpointIsSN

/-- Direct identity-M04 SN case for identity reflexivity with an
explicit endpoint SN premise. -/
theorem Term.identity_refl_isStronglyNormalizing_of_endpoint
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.refl (context := sourceCtx) carrier rawWitness) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.refl (context := sourceCtx) carrier rawWitness)
    (Reducible.fundamental_refl_at_id_of_endpoint
      (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
      (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
      (RawTerm.subst_identity_isStronglyNormalizing endpointIsSN))

/-- Direct identity-M04 SN case for observational reflexivity with an
explicit endpoint SN premise. -/
theorem Term.identity_oeqRefl_isStronglyNormalizing_of_endpoint
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.oeqRefl (context := sourceCtx) carrier rawWitness)
    (Reducible.fundamental_oeqRefl_at_oeq_of_endpoint
      (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
      (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
      (RawTerm.subst_identity_isStronglyNormalizing endpointIsSN))

/-- Direct identity-M04 SN case for strict reflexivity with an explicit
endpoint SN premise. -/
theorem Term.identity_idStrictRefl_isStronglyNormalizing_of_endpoint
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.idStrictRefl (context := sourceCtx)
        modeIsStrict carrier rawWitness) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.idStrictRefl (context := sourceCtx)
      modeIsStrict carrier rawWitness)
    (Reducible.fundamental_idStrictRefl_at_idStrict_of_endpoint
      (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
      (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
      modeIsStrict
      (RawTerm.subst_identity_isStronglyNormalizing endpointIsSN))

/-- Direct M04 SN endpoint for identity reflexivity with explicit endpoint
SN evidence. -/
theorem Term.refl_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.refl (context := sourceCtx) carrier rawWitness) :=
  Term.identity_refl_isStronglyNormalizing_of_endpoint endpointIsSN

/-- Direct M04 SN endpoint for observational reflexivity with explicit
endpoint SN evidence. -/
theorem Term.oeqRefl_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) :=
  Term.identity_oeqRefl_isStronglyNormalizing_of_endpoint endpointIsSN

/-- Direct M04 SN endpoint for strict reflexivity with explicit endpoint
SN evidence. -/
theorem Term.idStrictRefl_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.idStrictRefl (context := sourceCtx)
        modeIsStrict carrier rawWitness) :=
  Term.identity_idStrictRefl_isStronglyNormalizing_of_endpoint
    modeIsStrict endpointIsSN

/-- M04 raw-payload evidence form of the direct identity SN case for
identity reflexivity. -/
theorem Term.identity_refl_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.refl (context := sourceCtx) carrier rawWitness)) :
    Term.isStronglyNormalizing
      (Term.refl (context := sourceCtx) carrier rawWitness) :=
  Term.identity_refl_isStronglyNormalizing_of_endpoint payloads

/-- M04 raw-payload evidence form of the direct identity SN case for
observational reflexivity. -/
theorem Term.identity_oeqRefl_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.oeqRefl (context := sourceCtx) carrier rawWitness)) :
    Term.isStronglyNormalizing
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) :=
  Term.identity_oeqRefl_isStronglyNormalizing_of_endpoint payloads

/-- M04 raw-payload evidence form of the direct identity SN case for
strict reflexivity. -/
theorem Term.identity_idStrictRefl_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {rawWitness : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.idStrictRefl (context := sourceCtx)
          modeIsStrict carrier rawWitness)) :
    Term.isStronglyNormalizing
      (Term.idStrictRefl (context := sourceCtx)
        modeIsStrict carrier rawWitness) :=
  Term.identity_idStrictRefl_isStronglyNormalizing_of_endpoint
    modeIsStrict payloads


end LeanFX2
