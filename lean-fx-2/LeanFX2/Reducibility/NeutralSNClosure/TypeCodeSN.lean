import LeanFX2.Reducibility.NeutralSNIntro.Codes

/-! # LeanFX2.Reducibility.NeutralSNClosure.TypeCodeSN

Typed SN wrappers for the 11 universe-code constructors
(`universeCode` / `arrowCode` / `piTyCode` / `sigmaTyCode` /
`productCode` / `sumCode` / `eitherCode` / `equivCode` /
`listCode` / `optionCode` / `idCode`).

Each wrapper is a thin typed shim over the matching raw SN witness
in `NeutralSNIntro/Codes`, supplied to the Kripke fundamental lemma
in `Reducibility/Kripke/Fundamental.lean`.

## Root status

Layer 3 metatheory leaf.  Kripke step-indexed reducibility consumes
these endpoints directly; the legacy Tait-era closure helpers that
once lived here (`RawTerm.isStronglyNormalizing_of_typeCode`, its
identity-substitution sibling, and the `Term.HasStronglyNormalizingRawPayloads`
schematic predicate) were excised when the bypass-free Kripke
refactor landed. -/

namespace LeanFX2


/-- Direct M04 SN endpoint for universe code. -/
theorem Term.universeCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.isStronglyNormalizing
      (Term.universeCode (context := sourceCtx)
        innerLevel outerLevel cumulOk levelLe) :=
  RawTerm.universeCode_isStronglyNormalizing innerLevel.toNat

/-- Direct M04 SN endpoint for arrow type code with explicit payload SN. -/
theorem Term.arrowCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.arrowCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  RawTerm.arrowCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Direct M04 SN endpoint for dependent Pi type code with explicit
payload SN. -/
theorem Term.piTyCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  RawTerm.piTyCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Direct M04 SN endpoint for dependent Sigma type code with explicit
payload SN. -/
theorem Term.sigmaTyCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  RawTerm.sigmaTyCode_isStronglyNormalizing
    domainCodeIsSN codomainCodeIsSN

/-- Direct M04 SN endpoint for product type code with explicit payload SN. -/
theorem Term.productCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsSN : RawTerm.isStronglyNormalizing firstCodeRaw)
    (secondCodeIsSN : RawTerm.isStronglyNormalizing secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  RawTerm.productCode_isStronglyNormalizing
    firstCodeIsSN secondCodeIsSN

/-- Direct M04 SN endpoint for sum type code with explicit payload SN. -/
theorem Term.sumCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  RawTerm.sumCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Direct M04 SN endpoint for either type code with explicit payload SN. -/
theorem Term.eitherCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.eitherCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  RawTerm.eitherCode_isStronglyNormalizing
    leftCodeIsSN rightCodeIsSN

/-- Direct M04 SN endpoint for equivalence type code with explicit
payload SN. -/
theorem Term.equivCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsSN :
      RawTerm.isStronglyNormalizing leftTypeCodeRaw)
    (rightTypeCodeIsSN :
      RawTerm.isStronglyNormalizing rightTypeCodeRaw) :
    Term.isStronglyNormalizing
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) :=
  RawTerm.equivCode_isStronglyNormalizing
    leftTypeCodeIsSN rightTypeCodeIsSN

/-- Direct M04 SN endpoint for list type code with explicit payload SN. -/
theorem Term.listCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  RawTerm.listCode_isStronglyNormalizing elementCodeIsSN

/-- Direct M04 SN endpoint for option type code with explicit payload SN. -/
theorem Term.optionCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  RawTerm.optionCode_isStronglyNormalizing elementCodeIsSN

/-- Direct M04 SN endpoint for identity type code with explicit payload SN. -/
theorem Term.idCode_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftRaw rightRaw : RawTerm scope}
    (typeCodeIsSN : RawTerm.isStronglyNormalizing typeCodeRaw)
    (leftIsSN : RawTerm.isStronglyNormalizing leftRaw)
    (rightIsSN : RawTerm.isStronglyNormalizing rightRaw) :
    Term.isStronglyNormalizing
      (Term.idCode (context := sourceCtx)
        outerLevel levelLe typeCodeRaw leftRaw rightRaw) :=
  RawTerm.idCode_isStronglyNormalizing
    typeCodeIsSN leftIsSN rightIsSN


end LeanFX2
