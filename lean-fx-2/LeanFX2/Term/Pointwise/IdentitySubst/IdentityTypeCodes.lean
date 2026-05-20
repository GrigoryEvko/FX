import LeanFX2.Term.Pointwise.IdentitySubst.IdentityStructural
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityTypeCodes

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

/-! ## Universe code cases -/

/-- Universe-code case for ordinary identity substitution. -/
theorem Term.subst_identity_universeCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.universeCode (context := context) innerLevel outerLevel
          cumulOk levelLe))
      (Term.universeCode (context := context) innerLevel outerLevel
        cumulOk levelLe) := by
  rfl

/-- Arrow type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_arrowCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.arrowCode (context := context) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.arrowCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.subst]
  exact Term.arrowCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity domainCodeRaw)
    (RawTerm.subst_identity codomainCodeRaw)

/-- Pi type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_piTyCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.piTyCode (context := context) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.piTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.subst]
  exact Term.piTyCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity domainCodeRaw)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope)
        codomainCodeRaw]
      exact RawTerm.subst_identity codomainCodeRaw)

/-- Sigma type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_sigmaTyCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sigmaTyCode (context := context) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.sigmaTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  simp only [Term.subst]
  exact Term.sigmaTyCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity domainCodeRaw)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope)
        codomainCodeRaw]
      exact RawTerm.subst_identity codomainCodeRaw)

/-- Product type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_productCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.productCode (context := context) outerLevel levelLe
          firstCodeRaw secondCodeRaw))
      (Term.productCode (context := context) outerLevel levelLe
        firstCodeRaw secondCodeRaw) := by
  simp only [Term.subst]
  exact Term.productCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity firstCodeRaw)
    (RawTerm.subst_identity secondCodeRaw)

/-- Sum type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_sumCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sumCode (context := context) outerLevel levelLe
          leftCodeRaw rightCodeRaw))
      (Term.sumCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  simp only [Term.subst]
  exact Term.sumCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity leftCodeRaw)
    (RawTerm.subst_identity rightCodeRaw)

/-- List type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_listCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.listCode (context := context) outerLevel levelLe
          elementCodeRaw))
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw) := by
  simp only [Term.subst]
  exact Term.listCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity elementCodeRaw)

/-- Option type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_optionCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.optionCode (context := context) outerLevel levelLe
          elementCodeRaw))
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw) := by
  simp only [Term.subst]
  exact Term.optionCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity elementCodeRaw)

/-- Either type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_eitherCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.eitherCode (context := context) outerLevel levelLe
          leftCodeRaw rightCodeRaw))
      (Term.eitherCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  simp only [Term.subst]
  exact Term.eitherCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity leftCodeRaw)
    (RawTerm.subst_identity rightCodeRaw)

/-- Identity type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_idCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.idCode (context := context) outerLevel levelLe
          typeCodeRaw leftRaw rightRaw))
      (Term.idCode (context := context) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw) := by
  simp only [Term.subst]
  exact Term.idCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity typeCodeRaw)
    (RawTerm.subst_identity leftRaw)
    (RawTerm.subst_identity rightRaw)

/-- Equivalence type-code case for ordinary identity substitution. -/
theorem Term.subst_identity_equivCode_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivCode (context := context) outerLevel levelLe
          leftTypeCodeRaw rightTypeCodeRaw))
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) := by
  simp only [Term.subst]
  exact Term.equivCode_HEq_congr outerLevel levelLe
    (RawTerm.subst_identity leftTypeCodeRaw)
    (RawTerm.subst_identity rightTypeCodeRaw)

end LeanFX2
