import LeanFX2.Term

/-! # Term/HEqCongr/Atomic/TypeCodes

Type-code HEq congruences. -/

namespace LeanFX2

/-- HEq congruence for universe-code values with shared proof fields. -/
theorem Term.universeCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    HEq
      (Term.universeCode (context := context) innerLevel outerLevel cumulOk
        levelLe)
      (Term.universeCode (context := context) innerLevel outerLevel cumulOk
        levelLe) := by
  rfl

/-- HEq congruence for arrow type-code values. -/
theorem Term.arrowCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw1 domainCodeRaw2 codomainCodeRaw1 codomainCodeRaw2 :
      RawTerm scope}
    (domainCodeRawEq : domainCodeRaw1 = domainCodeRaw2)
    (codomainCodeRawEq : codomainCodeRaw1 = codomainCodeRaw2) :
    HEq
      (Term.arrowCode (context := context) outerLevel levelLe domainCodeRaw1
        codomainCodeRaw1)
      (Term.arrowCode (context := context) outerLevel levelLe domainCodeRaw2
        codomainCodeRaw2) := by
  subst domainCodeRawEq
  subst codomainCodeRawEq
  rfl

/-- HEq congruence for pi type-code values. -/
theorem Term.piTyCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw1 domainCodeRaw2 : RawTerm scope}
    {codomainCodeRaw1 codomainCodeRaw2 : RawTerm (scope + 1)}
    (domainCodeRawEq : domainCodeRaw1 = domainCodeRaw2)
    (codomainCodeRawEq : codomainCodeRaw1 = codomainCodeRaw2) :
    HEq
      (Term.piTyCode (context := context) outerLevel levelLe domainCodeRaw1
        codomainCodeRaw1)
      (Term.piTyCode (context := context) outerLevel levelLe domainCodeRaw2
        codomainCodeRaw2) := by
  subst domainCodeRawEq
  subst codomainCodeRawEq
  rfl

/-- HEq congruence for sigma type-code values. -/
theorem Term.sigmaTyCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw1 domainCodeRaw2 : RawTerm scope}
    {codomainCodeRaw1 codomainCodeRaw2 : RawTerm (scope + 1)}
    (domainCodeRawEq : domainCodeRaw1 = domainCodeRaw2)
    (codomainCodeRawEq : codomainCodeRaw1 = codomainCodeRaw2) :
    HEq
      (Term.sigmaTyCode (context := context) outerLevel levelLe domainCodeRaw1
        codomainCodeRaw1)
      (Term.sigmaTyCode (context := context) outerLevel levelLe domainCodeRaw2
        codomainCodeRaw2) := by
  subst domainCodeRawEq
  subst codomainCodeRawEq
  rfl

/-- HEq congruence for product type-code values. -/
theorem Term.productCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw1 firstCodeRaw2 secondCodeRaw1 secondCodeRaw2 :
      RawTerm scope}
    (firstCodeRawEq : firstCodeRaw1 = firstCodeRaw2)
    (secondCodeRawEq : secondCodeRaw1 = secondCodeRaw2) :
    HEq
      (Term.productCode (context := context) outerLevel levelLe firstCodeRaw1
        secondCodeRaw1)
      (Term.productCode (context := context) outerLevel levelLe firstCodeRaw2
        secondCodeRaw2) := by
  subst firstCodeRawEq
  subst secondCodeRawEq
  rfl

/-- HEq congruence for sum type-code values. -/
theorem Term.sumCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw1 leftCodeRaw2 rightCodeRaw1 rightCodeRaw2 : RawTerm scope}
    (leftCodeRawEq : leftCodeRaw1 = leftCodeRaw2)
    (rightCodeRawEq : rightCodeRaw1 = rightCodeRaw2) :
    HEq
      (Term.sumCode (context := context) outerLevel levelLe leftCodeRaw1
        rightCodeRaw1)
      (Term.sumCode (context := context) outerLevel levelLe leftCodeRaw2
        rightCodeRaw2) := by
  subst leftCodeRawEq
  subst rightCodeRawEq
  rfl

/-- HEq congruence for list type-code values. -/
theorem Term.listCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw1 elementCodeRaw2 : RawTerm scope}
    (elementCodeRawEq : elementCodeRaw1 = elementCodeRaw2) :
    HEq
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw1)
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw2) := by
  subst elementCodeRawEq
  rfl

/-- HEq congruence for option type-code values. -/
theorem Term.optionCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw1 elementCodeRaw2 : RawTerm scope}
    (elementCodeRawEq : elementCodeRaw1 = elementCodeRaw2) :
    HEq
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw1)
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw2) := by
  subst elementCodeRawEq
  rfl

/-- HEq congruence for either type-code values. -/
theorem Term.eitherCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw1 leftCodeRaw2 rightCodeRaw1 rightCodeRaw2 : RawTerm scope}
    (leftCodeRawEq : leftCodeRaw1 = leftCodeRaw2)
    (rightCodeRawEq : rightCodeRaw1 = rightCodeRaw2) :
    HEq
      (Term.eitherCode (context := context) outerLevel levelLe leftCodeRaw1
        rightCodeRaw1)
      (Term.eitherCode (context := context) outerLevel levelLe leftCodeRaw2
        rightCodeRaw2) := by
  subst leftCodeRawEq
  subst rightCodeRawEq
  rfl

/-- HEq congruence for identity type-code values. -/
theorem Term.idCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw1 typeCodeRaw2 leftRaw1 leftRaw2 rightRaw1 rightRaw2 :
      RawTerm scope}
    (typeCodeRawEq : typeCodeRaw1 = typeCodeRaw2)
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2) :
    HEq
      (Term.idCode (context := context) outerLevel levelLe typeCodeRaw1
        leftRaw1 rightRaw1)
      (Term.idCode (context := context) outerLevel levelLe typeCodeRaw2
        leftRaw2 rightRaw2) := by
  subst typeCodeRawEq
  subst leftRawEq
  subst rightRawEq
  rfl

/-- HEq congruence for equivalence type-code values. -/
theorem Term.equivCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw1 leftTypeCodeRaw2 rightTypeCodeRaw1 rightTypeCodeRaw2 :
      RawTerm scope}
    (leftTypeCodeRawEq : leftTypeCodeRaw1 = leftTypeCodeRaw2)
    (rightTypeCodeRawEq : rightTypeCodeRaw1 = rightTypeCodeRaw2) :
    HEq
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw1 rightTypeCodeRaw1)
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw2 rightTypeCodeRaw2) := by
  subst leftTypeCodeRawEq
  subst rightTypeCodeRawEq
  rfl

end LeanFX2
