import LeanFX2.Reducibility.FundamentalEliminators

/-! # LeanFX2.Reducibility.FundamentalAliases — SN aliases + K12.27 endpoints

The remaining SN-output endpoint aliases plus the K12.27 direct
M04 endpoints (the headline strong-normalization corollary cases).

## What ships

* Remaining SN-output endpoint aliases — short wrappers that
  re-expose existing fundamental-theorem outputs as Term SN
  witnesses for downstream consumption (M04 closure).
* K12.27 direct leaf M04 endpoints — base-case SN witnesses
  (unit / boolTrue / boolFalse / natZero / etc.) packaged as
  M04-headline-ready theorems.
* K12.27 direct recursive-intro M04 endpoints — recursive
  ctor SN witnesses (lam / pair / listCons / optionSome /
  natSucc / eitherInl/Inr / refl-witnesses) at the M04 level.
* K12.27 direct congruence-form M04 endpoints — congruence
  closures of M04 SN witnesses.
* K12.27 direct eliminator-form M04 endpoints — eliminator
  closures of M04 SN witnesses (app / fst / snd / boolElim /
  natElim / etc.).

## Root status

Layer 3 metatheory leaf.  Penultimate part of the K12.27 M04
strong-normalization corollary cascade. -/

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

/-- M04 raw-payload evidence form of the direct identity SN case for
arrow type code. -/
theorem Term.identity_arrowCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.arrowCode (context := sourceCtx)
          outerLevel levelLe domainCodeRaw codomainCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.arrowCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.identity_arrowCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2

/-- M04 raw-payload evidence form of the direct identity SN case for
Pi type code. -/
theorem Term.identity_piTyCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.piTyCode (context := sourceCtx)
          outerLevel levelLe domainCodeRaw codomainCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.identity_piTyCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2

/-- M04 raw-payload evidence form of the direct identity SN case for
Sigma type code. -/
theorem Term.identity_sigmaTyCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.sigmaTyCode (context := sourceCtx)
          outerLevel levelLe domainCodeRaw codomainCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.identity_sigmaTyCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2

/-- M04 raw-payload evidence form of the direct identity SN case for
product type code. -/
theorem Term.identity_productCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.productCode (context := sourceCtx)
          outerLevel levelLe firstCodeRaw secondCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Term.identity_productCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2

/-- M04 raw-payload evidence form of the direct identity SN case for sum
type code. -/
theorem Term.identity_sumCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.sumCode (context := sourceCtx)
          outerLevel levelLe leftCodeRaw rightCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Term.identity_sumCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2

/-- M04 raw-payload evidence form of the direct identity SN case for
either type code. -/
theorem Term.identity_eitherCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.eitherCode (context := sourceCtx)
          outerLevel levelLe leftCodeRaw rightCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.eitherCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Term.identity_eitherCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2

/-- M04 raw-payload evidence form of the direct identity SN case for
equivalence type code. -/
theorem Term.identity_equivCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.equivCode (context := sourceCtx)
          outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) :=
  Term.identity_equivCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2

/-- M04 raw-payload evidence form of the direct identity SN case for list
type code. -/
theorem Term.identity_listCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.listCode (context := sourceCtx)
          outerLevel levelLe elementCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Term.identity_listCode_isStronglyNormalizing_of_typeCode_payload
    outerLevel levelLe payloads

/-- M04 raw-payload evidence form of the direct identity SN case for
option type code. -/
theorem Term.identity_optionCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.optionCode (context := sourceCtx)
          outerLevel levelLe elementCodeRaw)) :
    Term.isStronglyNormalizing
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Term.identity_optionCode_isStronglyNormalizing_of_typeCode_payload
    outerLevel levelLe payloads

/-- M04 raw-payload evidence form of the direct identity SN case for
identity type code. -/
theorem Term.identity_idCode_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftRaw rightRaw : RawTerm scope}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.idCode (context := sourceCtx)
          outerLevel levelLe typeCodeRaw leftRaw rightRaw)) :
    Term.isStronglyNormalizing
      (Term.idCode (context := sourceCtx)
        outerLevel levelLe typeCodeRaw leftRaw rightRaw) :=
  Term.identity_idCode_isStronglyNormalizing_of_typeCode_payloads
    outerLevel levelLe payloads.1 payloads.2.1 payloads.2.2

/-- Direct M04 SN case for the canonical pointwise reflexivity witness
used by funext. -/
theorem Term.funextRefl_isStronglyNormalizing_of_apply
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (applyIsSN : RawTerm.isStronglyNormalizing applyRaw) :
    Term.isStronglyNormalizing
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) :=
  RawTerm.lam_isStronglyNormalizing
    (RawTerm.refl_isStronglyNormalizing applyIsSN)

/-- Raw-payload evidence form of the direct M04 SN case for the
canonical pointwise reflexivity witness used by funext. -/
theorem Term.funextRefl_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw)) :
    Term.isStronglyNormalizing
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextRefl_isStronglyNormalizing_of_apply
    domainType codomainType payloads

/-- Canonical typed SN surface endpoint for `funextRefl`, retaining the
explicit raw-payload SN obligation carried by the schematic `applyRaw`
field. -/
theorem Term.funextRefl_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw)) :
    Term.isStronglyNormalizing
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextRefl_isStronglyNormalizing_of_rawPayloads
    domainType codomainType payloads

/-- Direct M04 SN case for the Id-typed funext reflexivity witness. -/
theorem Term.funextReflAtId_isStronglyNormalizing_of_apply
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (applyIsSN : RawTerm.isStronglyNormalizing applyRaw) :
    Term.isStronglyNormalizing
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) :=
  RawTerm.lam_isStronglyNormalizing
    (RawTerm.refl_isStronglyNormalizing applyIsSN)

/-- Raw-payload evidence form of the direct M04 SN case for the Id-typed
funext reflexivity witness. -/
theorem Term.funextReflAtId_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw)) :
    Term.isStronglyNormalizing
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextReflAtId_isStronglyNormalizing_of_apply
    domainType codomainType payloads

/-- Canonical typed SN surface endpoint for `funextReflAtId`, retaining
the explicit raw-payload SN obligation carried by the schematic
`applyRaw` field. -/
theorem Term.funextReflAtId_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw)) :
    Term.isStronglyNormalizing
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextReflAtId_isStronglyNormalizing_of_rawPayloads
    domainType codomainType payloads

/-- Direct M04 SN case for heterogeneous funext introduction.  The current
raw projection contains `applyARaw`; `applyBRaw` occurs only in the static
type endpoints. -/
theorem Term.funextIntroHet_isStronglyNormalizing_of_applyLeft
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyARaw applyBRaw : RawTerm (scope + 1)}
    (applyLeftIsSN : RawTerm.isStronglyNormalizing applyARaw) :
    Term.isStronglyNormalizing
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) :=
  RawTerm.lam_isStronglyNormalizing
    (RawTerm.refl_isStronglyNormalizing applyLeftIsSN)

/-- Raw-payload evidence form of the direct M04 SN case for heterogeneous
funext introduction. -/
theorem Term.funextIntroHet_isStronglyNormalizing_of_rawPayloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyARaw applyBRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw)) :
    Term.isStronglyNormalizing
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) :=
  Term.funextIntroHet_isStronglyNormalizing_of_applyLeft
    domainType codomainType payloads

/-- Canonical typed SN surface endpoint for `funextIntroHet`, retaining
the explicit raw-payload SN obligation carried by the projected
`applyARaw` field. -/
theorem Term.funextIntroHet_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyARaw applyBRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw)) :
    Term.isStronglyNormalizing
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) :=
  Term.funextIntroHet_isStronglyNormalizing_of_rawPayloads
    domainType codomainType payloads

/-- **K12.27 identity-substitution funext-refl SN endpoint**.

The canonical funext witness carries a schematic `applyRaw` payload in
the raw projection.  The identity route therefore requires explicit SN
of that payload; identity lifting preserves it before
`Term.strong_normalization_of_identity_subst` erases the surrounding
identity substitution. -/
theorem Reducible.fundamental_identity_funextRefl_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw)) :
    Term.isStronglyNormalizing
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.strong_normalization_of_identity_subst
    (Term.funextRefl (context := sourceCtx)
      domainType codomainType applyRaw)
    (by
      change RawTerm.isStronglyNormalizing
        (RawTerm.lam
          (RawTerm.refl
            (applyRaw.subst ((@Subst.identity level scope).forRaw.lift))))
      exact RawTerm.lam_isStronglyNormalizing
        (RawTerm.refl_isStronglyNormalizing
          (RawTerm.subst_identity_lift_isStronglyNormalizing payloads)))

/-- **K12.27 identity-substitution Id-typed funext-refl SN endpoint**. -/
theorem Reducible.fundamental_identity_funextReflAtId_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw)) :
    Term.isStronglyNormalizing
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.strong_normalization_of_identity_subst
    (Term.funextReflAtId (context := sourceCtx)
      domainType codomainType applyRaw)
    (by
      change RawTerm.isStronglyNormalizing
        (RawTerm.lam
          (RawTerm.refl
            (applyRaw.subst ((@Subst.identity level scope).forRaw.lift))))
      exact RawTerm.lam_isStronglyNormalizing
        (RawTerm.refl_isStronglyNormalizing
          (RawTerm.subst_identity_lift_isStronglyNormalizing payloads)))

/-- **K12.27 identity-substitution heterogeneous funext SN endpoint**.

Only `applyARaw` appears in the projected raw term; `applyBRaw` appears
in the static identity type and is intentionally not an M04 raw-SN
obligation. -/
theorem Reducible.fundamental_identity_funextIntroHet_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyARaw applyBRaw : RawTerm (scope + 1)}
    (payloads :
      Term.HasStronglyNormalizingRawPayloads
        (Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw)) :
    Term.isStronglyNormalizing
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) :=
  Term.strong_normalization_of_identity_subst
    (Term.funextIntroHet (context := sourceCtx)
      domainType codomainType applyARaw applyBRaw)
    (by
      change RawTerm.isStronglyNormalizing
        (RawTerm.lam
          (RawTerm.refl
            (applyARaw.subst ((@Subst.identity level scope).forRaw.lift))))
      exact RawTerm.lam_isStronglyNormalizing
        (RawTerm.refl_isStronglyNormalizing
          (RawTerm.subst_identity_lift_isStronglyNormalizing payloads)))

/-! ## K12.27 direct leaf M04 endpoints -/

/-- Direct M04 SN case for typed variables. -/
theorem Term.var_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (position : Fin scope) :
    Term.isStronglyNormalizing
      (Term.var (context := sourceCtx) position) :=
  RawTerm.var_isStronglyNormalizing position

/-- Direct M04 SN case for the unit value. -/
theorem Term.unit_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.unit (context := sourceCtx)) :=
  RawTerm.unit_isStronglyNormalizing

/-- Direct M04 SN case for `true`. -/
theorem Term.boolTrue_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.boolTrue (context := sourceCtx)) :=
  RawTerm.boolTrue_isStronglyNormalizing

/-- Direct M04 SN case for `false`. -/
theorem Term.boolFalse_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.boolFalse (context := sourceCtx)) :=
  RawTerm.boolFalse_isStronglyNormalizing

/-- Direct M04 SN case for zero. -/
theorem Term.natZero_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.natZero (context := sourceCtx)) :=
  RawTerm.natZero_isStronglyNormalizing

/-- Direct M04 SN case for the empty list. -/
theorem Term.listNil_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.isStronglyNormalizing
      (Term.listNil (context := sourceCtx)
        (elementType := elementType)) :=
  RawTerm.listNil_isStronglyNormalizing

/-- Direct M04 SN case for `None`. -/
theorem Term.optionNone_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.isStronglyNormalizing
      (Term.optionNone (context := sourceCtx)
        (elementType := elementType)) :=
  RawTerm.optionNone_isStronglyNormalizing

/-- Direct M04 SN case for the left interval endpoint. -/
theorem Term.interval0_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.interval0 (context := sourceCtx)) :=
  RawTerm.interval0_isStronglyNormalizing

/-- Direct M04 SN case for the right interval endpoint. -/
theorem Term.interval1_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.interval1 (context := sourceCtx)) :=
  RawTerm.interval1_isStronglyNormalizing

/-! ## K12.27 direct recursive-intro M04 endpoints -/

/-- Direct M04 SN case for successor. -/
theorem Term.natSucc_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (predecessorIsSN : Term.isStronglyNormalizing predecessor) :
    Term.isStronglyNormalizing (Term.natSucc predecessor) :=
  RawTerm.natSucc_isStronglyNormalizing predecessorIsSN

/-- Direct M04 SN case for list cons. -/
theorem Term.listCons_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headIsSN : Term.isStronglyNormalizing headTerm)
    (tailIsSN : Term.isStronglyNormalizing tailTerm) :
    Term.isStronglyNormalizing
      (Term.listCons headTerm tailTerm) :=
  RawTerm.listCons_isStronglyNormalizing headIsSN tailIsSN

/-- Direct M04 SN case for `Some`. -/
theorem Term.optionSome_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing (Term.optionSome valueTerm) :=
  RawTerm.optionSome_isStronglyNormalizing valueIsSN

/-- Direct M04 SN case for left injection. -/
theorem Term.eitherInl_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing
      (Term.eitherInl (rightType := rightType) valueTerm) :=
  RawTerm.eitherInl_isStronglyNormalizing valueIsSN

/-- Direct M04 SN case for right injection. -/
theorem Term.eitherInr_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing
      (Term.eitherInr (leftType := leftType) valueTerm) :=
  RawTerm.eitherInr_isStronglyNormalizing valueIsSN

/-- Direct M04 SN case for interval negation. -/
theorem Term.intervalOpp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerValue) :
    Term.isStronglyNormalizing (Term.intervalOpp innerValue) :=
  RawTerm.intervalOpp_isStronglyNormalizing innerIsSN

/-- Direct M04 SN case for interval meet. -/
theorem Term.intervalMeet_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsSN : Term.isStronglyNormalizing leftValue)
    (rightIsSN : Term.isStronglyNormalizing rightValue) :
    Term.isStronglyNormalizing
      (Term.intervalMeet leftValue rightValue) :=
  RawTerm.intervalMeet_isStronglyNormalizing leftIsSN rightIsSN

/-- Direct M04 SN case for interval join. -/
theorem Term.intervalJoin_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsSN : Term.isStronglyNormalizing leftValue)
    (rightIsSN : Term.isStronglyNormalizing rightValue) :
    Term.isStronglyNormalizing
      (Term.intervalJoin leftValue rightValue) :=
  RawTerm.intervalJoin_isStronglyNormalizing leftIsSN rightIsSN

/-- Direct M04 SN case for modal introduction. -/
theorem Term.modIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modIntro innerTerm) :=
  RawTerm.modIntro_isStronglyNormalizing innerIsSN

/-- Direct M04 SN case for modal subsumption. -/
theorem Term.subsume_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.subsume innerTerm) :=
  RawTerm.subsume_isStronglyNormalizing innerIsSN

/-! ## K12.27 direct congruence-form M04 endpoints -/

/-- Direct M04 SN case for observational funext. -/
theorem Term.oeqFunext_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (pointwiseIsSN : Term.isStronglyNormalizing pointwiseProof) :
    Term.isStronglyNormalizing
      (Term.oeqFunext domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof) :=
  RawTerm.oeqFunext_isStronglyNormalizing pointwiseIsSN

/-- Direct M04 SN case for session receive. -/
theorem Term.sessionRecv_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIsSN : Term.isStronglyNormalizing channel) :
    Term.isStronglyNormalizing (Term.sessionRecv channel) :=
  RawTerm.sessionRecv_isStronglyNormalizing channelIsSN

/-- Direct M04 SN case for session send. -/
theorem Term.sessionSend_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelIsSN : Term.isStronglyNormalizing channel)
    (payloadIsSN : Term.isStronglyNormalizing payload) :
    Term.isStronglyNormalizing
      (Term.sessionSend protocolStep channel payload) :=
  RawTerm.sessionSend_isStronglyNormalizing channelIsSN payloadIsSN

/-- Direct M04 SN case for algebraic effect perform. -/
theorem Term.effectPerform_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIsSN : Term.isStronglyNormalizing operationTag)
    (argumentsAreSN : Term.isStronglyNormalizing arguments) :
    Term.isStronglyNormalizing
      (Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments) :=
  RawTerm.effectPerform_isStronglyNormalizing operationIsSN argumentsAreSN

/-- Direct M04 SN case for universe cumulativity markers. -/
theorem Term.cumulUp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (typeCodeIsSN : Term.isStronglyNormalizing typeCode) :
    Term.isStronglyNormalizing
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) :=
  RawTerm.cumulUpMarker_isStronglyNormalizing typeCodeIsSN

/-- Direct M04 SN case for the canonical identity equivalence. -/
theorem Term.equivReflId_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope) :
    Term.isStronglyNormalizing
      (Term.equivReflId (context := sourceCtx) carrier) := by
  let identityVar : Fin (scope + 1) := ⟨0, Nat.zero_lt_succ scope⟩
  have identityBodyIsSN :
      RawTerm.isStronglyNormalizing (RawTerm.var identityVar) :=
    RawTerm.var_isStronglyNormalizing identityVar
  have identityFunctionIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.lam (RawTerm.var identityVar)) :=
    RawTerm.lam_isStronglyNormalizing identityBodyIsSN
  exact RawTerm.equivIntro_isStronglyNormalizing
    identityFunctionIsSN identityFunctionIsSN

/-- Direct M04 SN case for the universe-identity view of the canonical
identity equivalence. -/
theorem Term.equivReflIdAtId_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Term.isStronglyNormalizing
      (Term.equivReflIdAtId (context := sourceCtx)
        innerLevel innerLevelLt carrier carrierRaw) := by
  let identityVar : Fin (scope + 1) := ⟨0, Nat.zero_lt_succ scope⟩
  have identityBodyIsSN :
      RawTerm.isStronglyNormalizing (RawTerm.var identityVar) :=
    RawTerm.var_isStronglyNormalizing identityVar
  have identityFunctionIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.lam (RawTerm.var identityVar)) :=
    RawTerm.lam_isStronglyNormalizing identityBodyIsSN
  exact RawTerm.equivIntro_isStronglyNormalizing
    identityFunctionIsSN identityFunctionIsSN

/-- Direct M04 SN case for heterogeneous univalence introduction.

The raw projection is definitionally the same as the packaged equivalence
witness, so the SN evidence is reused directly. -/
theorem Term.uaIntroHet_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivWitnessIsSN : Term.isStronglyNormalizing equivWitness) :
    Term.isStronglyNormalizing
      (Term.uaIntroHet innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) :=
  equivWitnessIsSN

/-- Direct M04 SN case for univalence-to-equivalence extraction. -/
theorem Term.uaToEquiv_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt)
          leftTyRaw rightTyRaw)
        proofRaw}
    (proofIsSN : Term.isStronglyNormalizing proof) :
    Term.isStronglyNormalizing
      (Term.uaToEquiv innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) :=
  RawTerm.uaToEquiv_isStronglyNormalizing proofIsSN

/-! ## K12.27 direct eliminator-form M04 endpoints -/

/-- Direct M04 SN case for boolean elimination. -/
theorem Term.boolElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue)
        thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse)
        elseRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (thenIsSN : Term.isStronglyNormalizing thenBranch)
    (elseIsSN : Term.isStronglyNormalizing elseBranch) :
    Term.isStronglyNormalizing
      (Term.boolElim scrutinee thenBranch elseBranch) :=
  RawTerm.boolElim_isStronglyNormalizing thenIsSN elseIsSN scrutineeIsSN

/-- Direct M04 SN case for identity elimination. -/
theorem Term.idJ_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.idJ baseCase witness) :=
  RawTerm.idJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- Direct M04 SN case for observational equality elimination. -/
theorem Term.oeqJ_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.oeqJ baseCase witness) :=
  RawTerm.oeqJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- Direct M04 SN case for strict identity elimination. -/
theorem Term.idStrictRec_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing
      (Term.idStrictRec modeIsStrict baseCase witness) :=
  RawTerm.idStrictRec_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- Fundamental case: `Term.equivApp` at `Ty.equiv` (K12.23.A).

First fundamental atomic over HOTT-adjacent eliminators.  Same
binary Reducible-composition pattern as K12.21.A
`fundamental_app_at_arrow` — `Term.equivApp` is the kernel-
internal application form for type equivalences (per K11.B8 docs
in `Term.lean:1029`+), mirroring `Term.app`'s shape exactly:
takes the equivalence + an argument at carrierA, produces a
result at carrierB.

K12.11's equiv closure ships the FULL Reducible (not SN-fallback)
on the output side, because both carriers (carrierA, carrierB)
are strict sub-Ty of `Ty.equiv carrierA carrierB` — the closure
can recurse on both via def-by-recursion on Ty:

    Reducible (Ty.equiv carrierA carrierB) equivTerm =
      SN(equivTerm) ∧ ∀ argumentTerm,
        Reducible carrierA argumentTerm →
        Reducible carrierB (Term.equivApp equivTerm argumentTerm)

The fundamental atomic projects the second conjunct and applies
to the substituted argument:

    equivIH.2 (Term.subst termSubst argumentTerm) argumentIH

`Term.subst` commutes over `.equivApp` definitionally
(`Term/Subst.lean:414` — no cast, since `Ty.equiv.subst` is
also definitional per `Foundation/Subst.lean:142`).  Same audit
gate as the existing K12.21 cluster.

Note: `Term.equivApply` (the D3.6-P4 univalence-target ctor at
`Term.lean:990`+) is a SEPARATE constructor projecting to a
different raw form; its fundamental case will ship as K12.23.B
once we audit which closure governs it. -/
theorem Reducible.fundamental_equivApp_at_equiv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIH :
        Reducible ((Ty.equiv carrierA carrierB).subst sigma)
                  (Term.subst termSubst equivTerm))
    (argumentIH :
        Reducible (carrierA.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Reducible (carrierB.subst sigma)
              (Term.subst termSubst (Term.equivApp equivTerm argumentTerm)) :=
  equivIH.2 (Term.subst termSubst argumentTerm) argumentIH

/-- Equivalence application preserves fundamental stability. -/
theorem Reducible.fundamental_equivApp_at_equiv_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIsStable :
      IsRenamingStableReducible
        ((Ty.equiv carrierA carrierB).subst sigma)
        (Term.subst termSubst equivTerm))
    (argumentIsStable :
      IsRenamingStableReducible (carrierA.subst sigma)
        (Term.subst termSubst argumentTerm)) :
    IsRenamingStableReducible (carrierB.subst sigma)
      (Term.subst termSubst
        (Term.equivApp equivTerm argumentTerm)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact (equivIsStable rhoIsInjective termRenaming).2
    (Term.rename termRenaming (Term.subst termSubst argumentTerm))
    (argumentIsStable rhoIsInjective termRenaming)

/-- Fundamental case: `Term.equivApply` at `Ty.equiv`
(K12.23.E, SN-output endpoint).

`Term.equivApply` is distinct from `Term.equivApp`: it projects to
`RawTerm.equivApply`, whose current raw fragment includes ua-refl beta
arms returning argument reducts.  The present `Ty.equiv` candidate stores
full Reducible closure for `equivApp`, not for this univalence-target raw
form, so this endpoint deliberately states the M04-relevant SN conclusion
only. -/
theorem Reducible.fundamental_equivApply_at_equiv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm :
        Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivIH :
        Reducible ((Ty.equiv carrierA carrierB).subst sigma)
                  (Term.subst termSubst equivTerm))
    (argumentIH :
        Reducible (carrierA.subst sigma)
                  (Term.subst termSubst argumentTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst (Term.equivApply equivTerm argumentTerm)) :=
  Term.equivApply_isStronglyNormalizing
    (Reducible.isStronglyNormalizing equivIH)
    (Reducible.isStronglyNormalizing argumentIH)

/-- Fundamental SN endpoint: `Term.equivIntroHet` at `Ty.equiv`
(K12.26 support).

The current `Ty.equiv` candidate stores full `equivApp` closure.
Building that closure for a freshly introduced equivalence would need
a backward bridge from `equivApp (equivIntro forward backward) arg` to
`app forward arg`, which is still tracked under the general
head-β/ι expansion work.  This endpoint therefore records only the
M04-relevant SN fact for the constructor raw form. -/
theorem Reducible.fundamental_equivIntroHet_at_equiv_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIH :
      Reducible ((Ty.arrow carrierA carrierB).subst sigma)
        (Term.subst termSubst forward))
    (backwardIH :
      Reducible ((Ty.arrow carrierB carrierA).subst sigma)
        (Term.subst termSubst backward)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.equivIntroHet forward backward leftInv rightInv)) :=
  Term.equivIntroHet_isStronglyNormalizing
    (Reducible.isStronglyNormalizing forwardIH)
    (Reducible.isStronglyNormalizing backwardIH)

/-- Fundamental SN endpoint: `Term.equivIntroHet` at `Ty.equiv`
(K12.26 support).

The conclusion is the M04-relevant Tait endpoint for the current
equivalence-introduction constructor: the introduced equivalence is
strongly normalizing whenever its forward and backward functions are
reducible.  The historical `_sn` theorem remains available as a
compatibility alias target. -/
theorem Reducible.fundamental_equivIntroHet_at_equiv
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardIH :
      Reducible ((Ty.arrow carrierA carrierB).subst sigma)
        (Term.subst termSubst forward))
    (backwardIH :
      Reducible ((Ty.arrow carrierB carrierA).subst sigma)
        (Term.subst termSubst backward)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.equivIntroHet forward backward leftInv rightInv)) :=
  Reducible.fundamental_equivIntroHet_at_equiv_sn forwardIH backwardIH

/-- Fundamental case: `Term.oeqFunext` at `Ty.oeq` (K12.23.B).

The current `Ty.oeq` reducibility arm is weak-J shaped: SN of the
witness plus SN preservation for `Term.oeqJ` over every SN base case.
`Term.oeqFunext` has a typed pointwise proof subterm, so its SN follows
from that subterm's reducibility by `RawTerm.oeqFunext_isStronglyNormalizing`.
The `oeqJ` closure is pure congruence in the present raw reduction
fragment, discharged by `RawTerm.oeqJ_isStronglyNormalizing`. -/
theorem Reducible.fundamental_oeqFunext_at_oeq
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {leftFunctionRaw rightFunctionRaw pointwiseRaw : RawTerm scope}
    {pointwiseProof :
        Term sourceCtx
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRaw}
    (pointwiseIH :
        Reducible
          ((oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw).subst sigma)
          (Term.subst termSubst pointwiseProof)) :
    Reducible
      ((Ty.oeq (Ty.arrow domainType codomainType)
          leftFunctionRaw rightFunctionRaw).subst sigma)
      (Term.subst termSubst
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof)) := by
  let witnessIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.oeqFunext (pointwiseRaw.subst sigma.forRaw)) :=
    RawTerm.oeqFunext_isStronglyNormalizing
      (Reducible.isStronglyNormalizing pointwiseIH)
  exact ⟨witnessIsSN,
    fun {_motiveType} {_baseRaw} _baseCase baseIsSN =>
      RawTerm.oeqJ_isStronglyNormalizing baseIsSN witnessIsSN⟩


end LeanFX2
