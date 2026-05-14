import LeanFX2.Reducibility.TypedCR2Wrapup.TypeCodesFundamental

/-! # LeanFX2.Reducibility.TypedCR2Wrapup.TypeCodesSN

Direct identity-M04 SN witnesses for the type-code family
(`Term.identity_*_isStronglyNormalizing`) plus the `cumulUpMarker`
SN preservation and `fundamental_cumulUp` cases.

## Root status

Layer 3 metatheory leaf.  Fourth and final slice of the K12.20.U
wrap-up. -/

namespace LeanFX2


/-- Direct identity-M04 SN case for universe code. -/
theorem Term.identity_universeCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.isStronglyNormalizing
      (Term.universeCode (context := sourceCtx)
        innerLevel outerLevel cumulOk levelLe) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.universeCode (context := sourceCtx)
      innerLevel outerLevel cumulOk levelLe)
    (Reducible.fundamental_universeCode
      (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
      (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
      innerLevel outerLevel cumulOk levelLe)

/-- Direct identity-M04 SN case for arrow type code. -/
theorem Term.identity_arrowCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw)
    (codomainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.arrowCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.arrowCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw)
    (Reducible.fundamental_identity_arrowCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      domainCodeIsTypeCode codomainCodeIsTypeCode)

/-- Direct identity-M04 SN case for Pi type code. -/
theorem Term.identity_piTyCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw)
    (codomainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.piTyCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw)
    (Reducible.fundamental_identity_piTyCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      domainCodeIsTypeCode codomainCodeIsTypeCode)

/-- Direct identity-M04 SN case for Sigma type code. -/
theorem Term.identity_sigmaTyCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw : RawTerm scope}
    {secondCodeRaw : RawTerm (scope + 1)}
    (firstCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw)
    (secondCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.sigmaTyCode (context := sourceCtx)
      outerLevel levelLe firstCodeRaw secondCodeRaw)
    (Reducible.fundamental_identity_sigmaTyCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      firstCodeIsTypeCode secondCodeIsTypeCode)

/-- Direct identity-M04 SN case for product type code. -/
theorem Term.identity_productCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw)
    (secondCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.productCode (context := sourceCtx)
      outerLevel levelLe firstCodeRaw secondCodeRaw)
    (Reducible.fundamental_identity_productCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      firstCodeIsTypeCode secondCodeIsTypeCode)

/-- Direct identity-M04 SN case for sum type code. -/
theorem Term.identity_sumCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.sumCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw)
    (Reducible.fundamental_identity_sumCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      leftCodeIsTypeCode rightCodeIsTypeCode)

/-- Direct identity-M04 SN case for either type code. -/
theorem Term.identity_eitherCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.eitherCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.eitherCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw)
    (Reducible.fundamental_identity_eitherCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      leftCodeIsTypeCode rightCodeIsTypeCode)

/-- Direct identity-M04 SN case for equivalence type code. -/
theorem Term.identity_equivCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftTypeCodeRaw)
    (rightTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightTypeCodeRaw) :
    Term.isStronglyNormalizing
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.equivCode (context := sourceCtx)
      outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw)
    (Reducible.fundamental_identity_equivCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      leftTypeCodeIsTypeCode rightTypeCodeIsTypeCode)

/-- Direct identity-M04 SN case for list type code. -/
theorem Term.identity_listCode_isStronglyNormalizing_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.listCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw)
    (Reducible.fundamental_identity_listCode_of_typeCode_payload
      (sourceCtx := sourceCtx) outerLevel levelLe elementCodeIsTypeCode)

/-- Direct identity-M04 SN case for option type code. -/
theorem Term.identity_optionCode_isStronglyNormalizing_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.optionCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw)
    (Reducible.fundamental_identity_optionCode_of_typeCode_payload
      (sourceCtx := sourceCtx) outerLevel levelLe elementCodeIsTypeCode)

/-- Direct identity-M04 SN case for identity type code. -/
theorem Term.identity_idCode_isStronglyNormalizing_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftCodeRaw rightCodeRaw : RawTerm scope}
    (typeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode typeCodeRaw)
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.idCode (context := sourceCtx)
        outerLevel levelLe typeCodeRaw leftCodeRaw rightCodeRaw) :=
  Reducible.strong_normalization_of_identity_reducible
    (Term.idCode (context := sourceCtx)
      outerLevel levelLe typeCodeRaw leftCodeRaw rightCodeRaw)
    (Reducible.fundamental_identity_idCode_of_typeCode_payloads
      (sourceCtx := sourceCtx) outerLevel levelLe
      typeCodeIsTypeCode leftCodeIsSN rightCodeIsSN)

/-- **K12.20.BB.2 cumulUp fundamental case** — REAL cross-universe
cumulativity at the typed Term level (Phase CUMUL-2.6 Design D).
Source `Ty.universe lowerLevel levelLeLow` is SN-direct; output
`Ty.universe higherLevel levelLeHigh` is also SN-direct (per
`Reducibility.lean:330`).  `Term.subst` on `Term.cumulUp` reconstructs
the cumulUp ctor at the target scope with the recursively-substituted
inner typeCode (per `LeanFX2/Term/Subst.lean:388-393`); the typed
raw form is `RawTerm.cumulUpMarker (codeRaw.subst sigma.forRaw)`.
The `innerIH` is SN of the substituted inner; the K12.20.BB.1
cumulUpMarker SN helper closes the proof. -/
theorem Reducible.fundamental_cumulUp
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode :
        Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (innerIH :
        Reducible ((Ty.universe lowerLevel levelLeLow).subst sigma)
                  (Term.subst termSubst typeCode)) :
    Reducible ((Ty.universe higherLevel levelLeHigh).subst sigma)
              (Term.subst termSubst
                (Term.cumulUp lowerLevel higherLevel
                              cumulMonotone levelLeLow levelLeHigh
                              typeCode)) :=
  RawTerm.cumulUpMarker_isStronglyNormalizing innerIH

/-- Cumulativity markers preserve fundamental stability. -/
theorem Reducible.fundamental_cumulUp_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode :
        Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (innerIsStable :
        IsRenamingStableReducible
          ((Ty.universe lowerLevel levelLeLow).subst sigma)
          (Term.subst termSubst typeCode)) :
    IsRenamingStableReducible
      ((Ty.universe higherLevel levelLeHigh).subst sigma)
      (Term.subst termSubst
        (Term.cumulUp lowerLevel higherLevel
                      cumulMonotone levelLeLow levelLeHigh
                      typeCode)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  exact RawTerm.cumulUpMarker_isStronglyNormalizing
    (innerIsStable rhoIsInjective termRenaming)



end LeanFX2
