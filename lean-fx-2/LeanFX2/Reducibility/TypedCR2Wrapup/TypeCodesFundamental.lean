import LeanFX2.Reducibility.TypedCR2Wrapup.IntervalSessionEffect

/-! # LeanFX2.Reducibility.TypedCR2Wrapup.TypeCodesFundamental

Fundamental cases for the universe-code family
(`universeCode`/`arrowCode`/`piTyCode`/`sigmaTyCode`/`productCode`/
`sumCode`/`eitherCode`/`equivCode`/`listCode`/`optionCode`/`idCode`)
plus their identity-substitution companions.

## Root status

Layer 3 metatheory leaf.  Third slice of the K12.20.U wrap-up. -/

namespace LeanFX2


/-- **K12.20.AR.3 universeCode fundamental case** — universe-code
nullary intro at outer level.  Output `Ty.universe outerLevel
levelLe` is SN-direct (Reducibility.lean:330); `Term.subst` on
universeCode is identity (`LeanFX2/Term/Subst.lean:379-380`);
`Reducible Ty.universe _` unfolds to `Term.isStronglyNormalizing
_`.  Direct lift via the K12.20.AR.2 SN helper. -/
theorem Reducible.fundamental_universeCode
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.universeCode (context := sourceCtx)
                  innerLevel outerLevel cumulOk levelLe)) :=
  RawTerm.universeCode_isStronglyNormalizing innerLevel.toNat

/-- Universe-code introduction is stable under future-world renamings. -/
theorem Reducible.fundamental_universeCode_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsRenamingStableReducible ((Ty.universe outerLevel levelLe).subst sigma)
      (Term.subst termSubst
        (Term.universeCode (context := sourceCtx)
          innerLevel outerLevel cumulOk levelLe)) := by
  intro _renamedScope _renamedCtx _rho _rhoIsInjective _termRenaming
  exact RawTerm.universeCode_isStronglyNormalizing innerLevel.toNat

/-- Type-code arrow fundamental endpoint with explicit payload SN
premises.

`Term.arrowCode` stores schematic raw payloads rather than typed child
terms.  Since the raw reduction relation has congruence under
`RawTerm.arrowCode`, those payloads must be known strongly normalizing
after substitution.  This theorem names that obligation for the
identity-only M04 chain instead of hiding it behind an impossible
unconditional constructor case. -/
theorem Reducible.fundamental_arrowCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (domainCodeRaw.subst sigma.forRaw))
    (codomainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (codomainCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.arrowCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  RawTerm.arrowCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Type-code dependent-Pi fundamental endpoint with explicit payload
SN premises.

The codomain raw payload is scoped under the binder, so its substituted
SN premise is over `sigma.forRaw.lift`.  This is the binder-shaped
counterpart to `fundamental_arrowCode_of_payloads`. -/
theorem Reducible.fundamental_piTyCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (domainCodeRaw.subst sigma.forRaw))
    (codomainCodeIsSN :
      RawTerm.isStronglyNormalizing
        (codomainCodeRaw.subst sigma.forRaw.lift)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.piTyCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  RawTerm.piTyCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Type-code dependent-Sigma fundamental endpoint with explicit
payload SN premises.

The second raw payload is scoped under the binder, so the premise uses
`sigma.forRaw.lift`, matching `Term.subst` for `sigmaTyCode`. -/
theorem Reducible.fundamental_sigmaTyCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw : RawTerm scope}
    {secondCodeRaw : RawTerm (scope + 1)}
    (firstCodeIsSN :
      RawTerm.isStronglyNormalizing
        (firstCodeRaw.subst sigma.forRaw))
    (secondCodeIsSN :
      RawTerm.isStronglyNormalizing
        (secondCodeRaw.subst sigma.forRaw.lift)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.sigmaTyCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  RawTerm.sigmaTyCode_isStronglyNormalizing
    firstCodeIsSN secondCodeIsSN

/-- Type-code product fundamental endpoint with explicit same-scope
payload SN premises. -/
theorem Reducible.fundamental_productCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsSN :
      RawTerm.isStronglyNormalizing
        (firstCodeRaw.subst sigma.forRaw))
    (secondCodeIsSN :
      RawTerm.isStronglyNormalizing
        (secondCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.productCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  RawTerm.productCode_isStronglyNormalizing
    firstCodeIsSN secondCodeIsSN

/-- Type-code sum fundamental endpoint with explicit same-scope
payload SN premises. -/
theorem Reducible.fundamental_sumCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftCodeRaw.subst sigma.forRaw))
    (rightCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.sumCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  RawTerm.sumCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Type-code either fundamental endpoint with explicit same-scope
payload SN premises. -/
theorem Reducible.fundamental_eitherCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftCodeRaw.subst sigma.forRaw))
    (rightCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.eitherCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  RawTerm.eitherCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Type-code equivalence fundamental endpoint with explicit
same-scope payload SN premises. -/
theorem Reducible.fundamental_equivCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftTypeCodeRaw.subst sigma.forRaw))
    (rightTypeCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightTypeCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.equivCode (context := sourceCtx)
                  outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw)) :=
  RawTerm.equivCode_isStronglyNormalizing
    leftTypeCodeIsSN rightTypeCodeIsSN

/-- Type-code list fundamental endpoint with an explicit element-code
SN premise. -/
theorem Reducible.fundamental_listCode_of_payload
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN :
      RawTerm.isStronglyNormalizing
        (elementCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.listCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  RawTerm.listCode_isStronglyNormalizing elementCodeIsSN

/-- Type-code option fundamental endpoint with an explicit
element-code SN premise. -/
theorem Reducible.fundamental_optionCode_of_payload
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN :
      RawTerm.isStronglyNormalizing
        (elementCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.optionCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  RawTerm.optionCode_isStronglyNormalizing elementCodeIsSN

/-- Type-code identity fundamental endpoint with explicit carrier and
endpoint-code SN premises. -/
theorem Reducible.fundamental_idCode_of_payloads
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftCodeRaw rightCodeRaw : RawTerm scope}
    (typeCodeIsSN :
      RawTerm.isStronglyNormalizing
        (typeCodeRaw.subst sigma.forRaw))
    (leftCodeIsSN :
      RawTerm.isStronglyNormalizing
        (leftCodeRaw.subst sigma.forRaw))
    (rightCodeIsSN :
      RawTerm.isStronglyNormalizing
        (rightCodeRaw.subst sigma.forRaw)) :
    Reducible ((Ty.universe outerLevel levelLe).subst sigma)
              (Term.subst termSubst
                (Term.idCode (context := sourceCtx)
                  outerLevel levelLe
                  typeCodeRaw leftCodeRaw rightCodeRaw)) :=
  RawTerm.idCode_isStronglyNormalizing
    typeCodeIsSN leftCodeIsSN rightCodeIsSN

/-- Identity-substitution arrow-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_arrowCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode domainCodeRaw)
    (codomainCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode codomainCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.arrowCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  Reducible.fundamental_arrowCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      domainCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      codomainCodeIsTypeCode)

/-- Identity-substitution Pi-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_piTyCode_of_typeCode_payloads
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
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.piTyCode (context := sourceCtx)
                  outerLevel levelLe domainCodeRaw codomainCodeRaw)) :=
  Reducible.fundamental_piTyCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      domainCodeIsTypeCode)
    (RawTerm.subst_identity_lift_isStronglyNormalizing
      (RawTerm.isStronglyNormalizing_of_typeCode codomainCodeIsTypeCode))

/-- Identity-substitution Sigma-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_sigmaTyCode_of_typeCode_payloads
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
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.sigmaTyCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  Reducible.fundamental_sigmaTyCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      firstCodeIsTypeCode)
    (RawTerm.subst_identity_lift_isStronglyNormalizing
      (RawTerm.isStronglyNormalizing_of_typeCode secondCodeIsTypeCode))

/-- Identity-substitution product-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_productCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode firstCodeRaw)
    (secondCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode secondCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.productCode (context := sourceCtx)
                  outerLevel levelLe firstCodeRaw secondCodeRaw)) :=
  Reducible.fundamental_productCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      firstCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      secondCodeIsTypeCode)

/-- Identity-substitution sum-code endpoint from named type-code payload
evidence. -/
theorem Reducible.fundamental_identity_sumCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.sumCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  Reducible.fundamental_sumCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      leftCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      rightCodeIsTypeCode)

/-- Identity-substitution either-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_eitherCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftCodeRaw)
    (rightCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.eitherCode (context := sourceCtx)
                  outerLevel levelLe leftCodeRaw rightCodeRaw)) :=
  Reducible.fundamental_eitherCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      leftCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      rightCodeIsTypeCode)

/-- Identity-substitution equivalence-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_equivCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode leftTypeCodeRaw)
    (rightTypeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode rightTypeCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.equivCode (context := sourceCtx)
                  outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw)) :=
  Reducible.fundamental_equivCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      leftTypeCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      rightTypeCodeIsTypeCode)

/-- Identity-substitution list-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_listCode_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.listCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  Reducible.fundamental_listCode_of_payload
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      elementCodeIsTypeCode)

/-- Identity-substitution option-code endpoint from named type-code
payload evidence. -/
theorem Reducible.fundamental_identity_optionCode_of_typeCode_payload
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode elementCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.optionCode (context := sourceCtx)
                  outerLevel levelLe elementCodeRaw)) :=
  Reducible.fundamental_optionCode_of_payload
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      elementCodeIsTypeCode)

/-- Identity-substitution identity-code endpoint from named carrier-code
and endpoint SN evidence. -/
theorem Reducible.fundamental_identity_idCode_of_typeCode_payloads
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftCodeRaw rightCodeRaw : RawTerm scope}
    (typeCodeIsTypeCode :
      RawTerm.IsStronglyNormalizingTypeCode typeCodeRaw)
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Reducible ((Ty.universe outerLevel levelLe).subst Subst.identity)
              (Term.subst (TermSubst.identity sourceCtx)
                (Term.idCode (context := sourceCtx)
                  outerLevel levelLe
                  typeCodeRaw leftCodeRaw rightCodeRaw)) :=
  Reducible.fundamental_idCode_of_payloads
    (sourceCtx := sourceCtx) (targetCtx := sourceCtx)
    (sigma := Subst.identity) (termSubst := TermSubst.identity sourceCtx)
    outerLevel levelLe
    (RawTerm.subst_identity_isStronglyNormalizing_of_typeCode
      typeCodeIsTypeCode)
    (RawTerm.subst_identity_isStronglyNormalizing leftCodeIsSN)
    (RawTerm.subst_identity_isStronglyNormalizing rightCodeIsSN)


end LeanFX2
