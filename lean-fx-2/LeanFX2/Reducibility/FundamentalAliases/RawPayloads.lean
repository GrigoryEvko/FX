import LeanFX2.Reducibility.FundamentalAliases.Aliases

/-! # LeanFX2.Reducibility.FundamentalAliases.RawPayloads

M04 raw-payload SN witnesses: the
`Term.identity_*_isStronglyNormalizing_of_rawPayloads` family
for the refl trinity + universe / arrow / piTy / sigmaTy /
productCode / sumCode / eitherCode / equivCode / listCode /
optionCode / idCode type codes + funextRefl / pathCompose /
oeqTrans / equivCompose / sessionRecv / sessionSend /
effectPerform.

## Root status

Layer 3 metatheory leaf.  Second slice of FundamentalAliases. -/

namespace LeanFX2


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

end LeanFX2
