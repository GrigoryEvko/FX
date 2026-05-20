import LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeStructural
import LeanFX2.Term.HEqCongr.Compound
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityLikeTypeCodesAndHoTT

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

/-! ## Identity-like universe and type-code cases -/

/-- Universe-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_universeCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    HEq
      (Term.subst termSubst
        (Term.universeCode (context := sourceCtx) innerLevel outerLevel
          cumulOk levelLe))
      (Term.universeCode (context := sourceCtx) innerLevel outerLevel
        cumulOk levelLe) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  rfl

/-- Arrow type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_arrowCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.arrowCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.arrowCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq domainCodeRaw)
    (substitutionIsIdentityLike.rawSubst_eq codomainCodeRaw)

/-- Pi type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_piTyCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst termSubst
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.piTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.piTyCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq domainCodeRaw)
    ((substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq codomainCodeRaw)

/-- Sigma type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_sigmaTyCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst termSubst
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw))
      (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.sigmaTyCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq domainCodeRaw)
    ((substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq codomainCodeRaw)

/-- Product type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_productCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRaw secondCodeRaw))
      (Term.productCode (context := sourceCtx) outerLevel levelLe
        firstCodeRaw secondCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.productCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq firstCodeRaw)
    (substitutionIsIdentityLike.rawSubst_eq secondCodeRaw)

/-- Sum type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_sumCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw))
      (Term.sumCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.sumCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq leftCodeRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightCodeRaw)

/-- List type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_listCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw))
      (Term.listCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.listCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq elementCodeRaw)

/-- Option type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_optionCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw))
      (Term.optionCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.optionCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq elementCodeRaw)

/-- Either type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_eitherCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw))
      (Term.eitherCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.eitherCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq leftCodeRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightCodeRaw)

/-- Identity type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_idCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRaw leftRaw rightRaw))
      (Term.idCode (context := sourceCtx) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.idCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq typeCodeRaw)
    (substitutionIsIdentityLike.rawSubst_eq leftRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightRaw)

/-- Equivalence type-code case for an identity-like substitution. -/
theorem Term.subst_identityLike_equivCode_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRaw rightTypeCodeRaw))
      (Term.equivCode (context := sourceCtx) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.equivCode_HEq_congr outerLevel levelLe
    (substitutionIsIdentityLike.rawSubst_eq leftTypeCodeRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightTypeCodeRaw)

/-- Canonical identity equivalence case for an identity-like substitution. -/
theorem Term.subst_identityLike_equivReflId_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (carrier : Ty level scope) :
    HEq
      (Term.subst termSubst
        (Term.equivReflId (context := sourceCtx) carrier))
      (Term.equivReflId (context := sourceCtx) carrier) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.equivReflId_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrier)

/-- Id-typed identity equivalence case for an identity-like substitution. -/
theorem Term.subst_identityLike_equivReflIdAtId_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    HEq
      (Term.subst termSubst
        (Term.equivReflIdAtId (context := sourceCtx) innerLevel
          innerLevelLt carrier carrierRaw))
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel
        innerLevelLt carrier carrierRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.equivReflIdAtId_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq carrier)
    (substitutionIsIdentityLike.rawSubst_eq carrierRaw)

/-- Id-typed funext witness case for an identity-like substitution. -/
theorem Term.subst_identityLike_funextReflAtId_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst termSubst
        (Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw))
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.funextReflAtId_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq domainType)
    (substitutionIsIdentityLike.tySubst_eq codomainType)
    ((substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq applyRaw)

/-- Univalence beta extraction case for an identity-like substitution. -/
theorem Term.subst_identityLike_uaToEquiv_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofHEq :
      HEq (Term.subst termSubst proof) proof) :
    HEq
      (Term.subst termSubst
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
          leftTyRaw rightTyRaw proof))
      (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
        leftTyRaw rightTyRaw proof) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.uaToEquiv_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq leftTy)
    (substitutionIsIdentityLike.tySubst_eq rightTy)
    (substitutionIsIdentityLike.rawSubst_eq leftTyRaw)
    (substitutionIsIdentityLike.rawSubst_eq rightTyRaw)
    (substitutionIsIdentityLike.rawSubst_eq proofRaw)
    proofHEq

/-- Cubical transport case for an identity-like substitution. -/
theorem Term.subst_identityLike_transp_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term sourceCtx sourceType sourceRaw)
    (typePathHEq :
      HEq (Term.subst termSubst typePath) typePath)
    (sourceValueHEq :
      HEq (Term.subst termSubst sourceValue) sourceValue) :
    HEq
      (Term.subst termSubst
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType sourceTypeRaw targetTypeRaw typePath
          sourceValue))
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw typePath
        sourceValue) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.transp_HEq_congr
    modeIsUnivalent universeLevel universeLevelLt
    (substitutionIsIdentityLike.tySubst_eq sourceType)
    (substitutionIsIdentityLike.tySubst_eq targetType)
    (substitutionIsIdentityLike.rawSubst_eq sourceTypeRaw)
    (substitutionIsIdentityLike.rawSubst_eq targetTypeRaw)
    (substitutionIsIdentityLike.rawSubst_eq pathRaw)
    (substitutionIsIdentityLike.rawSubst_eq sourceRaw)
    typePathHEq sourceValueHEq

/-- Refinement introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_refineIntro_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term sourceCtx baseType valueRaw)
    (predicateProof : Term sourceCtx Ty.unit proofRaw)
    (baseValueHEq :
      HEq (Term.subst termSubst baseValue) baseValue)
    (predicateProofHEq :
      HEq (Term.subst termSubst predicateProof) predicateProof) :
    HEq
      (Term.subst termSubst
        (Term.refineIntro predicate baseValue predicateProof))
      (Term.refineIntro predicate baseValue predicateProof) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.refineIntro_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq baseType)
    ((substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq predicate)
    (substitutionIsIdentityLike.rawSubst_eq valueRaw)
    (substitutionIsIdentityLike.rawSubst_eq proofRaw)
    baseValueHEq predicateProofHEq

/-- Heterogeneous univalence introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_uaIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term sourceCtx (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessHEq :
      HEq (Term.subst termSubst equivWitness) equivWitness) :
    HEq
      (Term.subst termSubst
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
          equivWitness))
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.uaIntroHet_HEq_congr
    innerLevel innerLevelLt
    (substitutionIsIdentityLike.tySubst_eq carrierA)
    (substitutionIsIdentityLike.tySubst_eq carrierB)
    (substitutionIsIdentityLike.rawSubst_eq carrierARaw)
    (substitutionIsIdentityLike.rawSubst_eq carrierBRaw)
    (substitutionIsIdentityLike.rawSubst_eq forwardRaw)
    (substitutionIsIdentityLike.rawSubst_eq backwardRaw)
    equivWitnessHEq

/-- Heterogeneous funext introduction case for an identity-like substitution. -/
theorem Term.subst_identityLike_funextIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst termSubst
        (Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw))
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  exact Term.funextIntroHet_HEq_congr
    (substitutionIsIdentityLike.tySubst_eq domainType)
    (substitutionIsIdentityLike.tySubst_eq codomainType)
    ((substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq applyARaw)
    ((substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq applyBRaw)

/-- Canonical funext reflexivity case for an identity-like substitution. -/
theorem Term.subst_identityLike_funextRefl_HEq
    {mode : Mode} {level scope : Nat}
    {sourceCtx targetCtx : Ctx mode level scope}
    {sigma : Subst level scope scope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substitutionIsIdentityLike :
      TermSubst.IsIdentityLike termSubst)
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst termSubst
        (Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw))
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) := by
  have contextsEq : targetCtx = sourceCtx :=
    eq_of_heq substitutionIsIdentityLike.contextHEq
  subst contextsEq
  simp only [Term.subst]
  have applyRawIdentity :
      applyRaw.subst sigma.forRaw.lift = applyRaw :=
    (substitutionIsIdentityLike.lift Ty.unit).rawSubst_eq applyRaw
  have funextWithoutCastHEq :
      HEq
        (Term.funextRefl
          (context := targetCtx)
          (domainType.subst sigma)
          (codomainType.subst sigma)
          (applyRaw.subst sigma.forRaw.lift))
        (Term.funextRefl (context := targetCtx)
          domainType codomainType applyRaw) :=
    Term.funextRefl_HEq_congr
      (substitutionIsIdentityLike.tySubst_eq domainType)
      (substitutionIsIdentityLike.tySubst_eq codomainType)
      applyRawIdentity
  have resultCastHEq :
      HEq
        ((funextReflType_subst sigma domainType codomainType applyRaw).symm ▸
          Term.funextRefl
            (context := targetCtx)
            (domainType.subst sigma)
            (codomainType.subst sigma)
            (applyRaw.subst sigma.forRaw.lift))
        (Term.funextRefl
          (context := targetCtx)
          (domainType.subst sigma)
          (codomainType.subst sigma)
          (applyRaw.subst sigma.forRaw.lift)) := by
    exact Term.type_eq_cast_heq
      (funextReflType_subst sigma domainType codomainType applyRaw).symm
      (Term.funextRefl
        (context := targetCtx)
        (domainType.subst sigma)
        (codomainType.subst sigma)
        (applyRaw.subst sigma.forRaw.lift))
  exact HEq.trans resultCastHEq funextWithoutCastHEq

end LeanFX2
