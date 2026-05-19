import LeanFX2.Term.Pointwise.IdentitySubst.IdentityTypeCodes

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityHoTT

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

/-! ## HoTT canonical value cases -/

/-- Canonical identity equivalence case for ordinary identity substitution. -/
theorem Term.subst_identity_equivReflId_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivReflId (context := context) carrier))
      (Term.equivReflId (context := context) carrier) := by
  simp only [Term.subst]
  exact Term.equivReflId_HEq_congr (Ty.subst_identity carrier)

/-- Id-typed identity equivalence case for ordinary identity substitution. -/
theorem Term.subst_identity_equivReflIdAtId_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivReflIdAtId (context := context) innerLevel
          innerLevelLt carrier carrierRaw))
      (Term.equivReflIdAtId (context := context) innerLevel
        innerLevelLt carrier carrierRaw) := by
  simp only [Term.subst]
  exact Term.equivReflIdAtId_HEq_congr
    (Ty.subst_identity carrier)
    (RawTerm.subst_identity carrierRaw)

/-- Id-typed funext witness case for ordinary identity substitution. -/
theorem Term.subst_identity_funextReflAtId_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.funextReflAtId (context := context)
          domainType codomainType applyRaw))
      (Term.funextReflAtId (context := context)
        domainType codomainType applyRaw) := by
  simp only [Term.subst]
  exact Term.funextReflAtId_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) applyRaw]
      exact RawTerm.subst_identity applyRaw)

/-- Canonical funext reflexivity case for ordinary identity substitution. -/
theorem Term.subst_identity_funextRefl_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.funextRefl (context := context)
          domainType codomainType applyRaw))
      (Term.funextRefl (context := context)
        domainType codomainType applyRaw) := by
  simp only [Term.subst]
  have applyRawIdentity :
      applyRaw.subst (@Subst.identity level scope).forRaw.lift =
        applyRaw := by
    rw [RawTerm.subst_pointwise
      (@Subst.identity_lift_forRaw_pointwise level scope) applyRaw]
    exact RawTerm.subst_identity applyRaw
  have funextWithoutCastHEq :
      HEq
        (Term.funextRefl
          (context := context)
          (domainType.subst Subst.identity)
          (codomainType.subst Subst.identity)
          (applyRaw.subst (@Subst.identity level scope).forRaw.lift))
        (Term.funextRefl (context := context)
          domainType codomainType applyRaw) :=
    Term.funextRefl_HEq_congr
      (Ty.subst_identity domainType)
      (Ty.subst_identity codomainType)
      applyRawIdentity
  have resultCastHEq :
      HEq
        ((funextReflType_subst Subst.identity
          domainType codomainType applyRaw).symm ▸
          Term.funextRefl
            (context := context)
            (domainType.subst Subst.identity)
            (codomainType.subst Subst.identity)
            (applyRaw.subst
              (@Subst.identity level scope).forRaw.lift))
        (Term.funextRefl
          (context := context)
          (domainType.subst Subst.identity)
          (codomainType.subst Subst.identity)
          (applyRaw.subst
            (@Subst.identity level scope).forRaw.lift)) := by
    exact Term.type_eq_cast_heq
      (funextReflType_subst Subst.identity
        domainType codomainType applyRaw).symm
      (Term.funextRefl
        (context := context)
        (domainType.subst Subst.identity)
        (codomainType.subst Subst.identity)
        (applyRaw.subst
          (@Subst.identity level scope).forRaw.lift))
  exact HEq.trans resultCastHEq funextWithoutCastHEq

/-- Observational funext case for ordinary identity substitution. -/
theorem Term.subst_identity_oeqFunext_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    (pointwiseProof :
      Term context
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseHEq :
      HEq (Term.subst (TermSubst.identity context) pointwiseProof)
        pointwiseProof) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.oeqFunext domainType codomainType leftFunctionRaw
          rightFunctionRaw pointwiseProof))
      (Term.oeqFunext domainType codomainType leftFunctionRaw
        rightFunctionRaw pointwiseProof) := by
  simp only [Term.subst]
  have pointwiseCastHEq :
      HEq
        ((oeqFunextPointwiseType_subst Subst.identity domainType codomainType
          leftFunctionRaw rightFunctionRaw) ▸
          Term.subst (TermSubst.identity context) pointwiseProof)
        pointwiseProof :=
    HEq.trans
      (Term.type_eq_cast_heq
        (oeqFunextPointwiseType_subst Subst.identity domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        (Term.subst (TermSubst.identity context) pointwiseProof))
      pointwiseHEq
  exact Term.oeqFunext_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (RawTerm.subst_identity leftFunctionRaw)
    (RawTerm.subst_identity rightFunctionRaw)
    (RawTerm.subst_identity pointwiseRaw)
    pointwiseCastHEq

/-- Cubical transport case for ordinary identity substitution. -/
theorem Term.subst_identity_transp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term context sourceType sourceRaw)
    (typePathHEq :
      HEq (Term.subst (TermSubst.identity context) typePath)
        typePath)
    (sourceValueHEq :
      HEq (Term.subst (TermSubst.identity context) sourceValue)
        sourceValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType targetType sourceTypeRaw targetTypeRaw typePath
          sourceValue))
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw typePath
        sourceValue) := by
  simp only [Term.subst]
  exact Term.transp_HEq_congr
    modeIsUnivalent universeLevel universeLevelLt
    (Ty.subst_identity sourceType)
    (Ty.subst_identity targetType)
    (RawTerm.subst_identity sourceTypeRaw)
    (RawTerm.subst_identity targetTypeRaw)
    (RawTerm.subst_identity pathRaw)
    (RawTerm.subst_identity sourceRaw)
    typePathHEq sourceValueHEq

/-- Refinement introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_refineIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw)
    (baseValueHEq :
      HEq (Term.subst (TermSubst.identity context) baseValue)
        baseValue)
    (predicateProofHEq :
      HEq (Term.subst (TermSubst.identity context) predicateProof)
        predicateProof) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.refineIntro predicate baseValue predicateProof))
      (Term.refineIntro predicate baseValue predicateProof) := by
  simp only [Term.subst]
  exact Term.refineIntro_HEq_congr
    (Ty.subst_identity baseType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) predicate]
      exact RawTerm.subst_identity predicate)
    (RawTerm.subst_identity valueRaw)
    (RawTerm.subst_identity proofRaw)
    baseValueHEq predicateProofHEq

/-- Heterogeneous univalence introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_uaIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term context (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessHEq :
      HEq (Term.subst (TermSubst.identity context) equivWitness)
        equivWitness) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
          equivWitness))
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness) := by
  simp only [Term.subst]
  exact Term.uaIntroHet_HEq_congr
    innerLevel innerLevelLt
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity carrierARaw)
    (RawTerm.subst_identity carrierBRaw)
    (RawTerm.subst_identity forwardRaw)
    (RawTerm.subst_identity backwardRaw)
    equivWitnessHEq

/-- Heterogeneous equivalence introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_equivIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardHEq :
      HEq (Term.subst (TermSubst.identity context) forward) forward)
    (backwardHEq :
      HEq (Term.subst (TermSubst.identity context) backward) backward)
    (leftInvHEq :
      HEq (Term.subst (TermSubst.identity context) leftInv) leftInv)
    (rightInvHEq :
      HEq (Term.subst (TermSubst.identity context) rightInv) rightInv) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivIntroHet forward backward leftInv rightInv))
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  simp only [Term.subst]
  have leftInvCastHEq :
      HEq
        ((equivIntroHetLeftInverseType_subst Subst.identity
          carrierA forwardRaw backwardRaw) ▸
          Term.subst (TermSubst.identity context) leftInv)
        leftInv :=
    HEq.trans
      (Term.type_eq_cast_heq
        (equivIntroHetLeftInverseType_subst Subst.identity
          carrierA forwardRaw backwardRaw)
        (Term.subst (TermSubst.identity context) leftInv))
      leftInvHEq
  have rightInvCastHEq :
      HEq
        ((equivIntroHetRightInverseType_subst Subst.identity
          carrierB forwardRaw backwardRaw) ▸
          Term.subst (TermSubst.identity context) rightInv)
        rightInv :=
    HEq.trans
      (Term.type_eq_cast_heq
        (equivIntroHetRightInverseType_subst Subst.identity
          carrierB forwardRaw backwardRaw)
        (Term.subst (TermSubst.identity context) rightInv))
      rightInvHEq
  exact Term.equivIntroHet_HEq_congr
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity forwardRaw)
    (RawTerm.subst_identity backwardRaw)
    (RawTerm.subst_identity leftInvRaw)
    (RawTerm.subst_identity rightInvRaw)
    forwardHEq backwardHEq leftInvCastHEq rightInvCastHEq

/-- Heterogeneous funext introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_funextIntroHet_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.funextIntroHet (context := context)
          domainType codomainType applyARaw applyBRaw))
      (Term.funextIntroHet (context := context)
        domainType codomainType applyARaw applyBRaw) := by
  simp only [Term.subst]
  exact Term.funextIntroHet_HEq_congr
    (Ty.subst_identity domainType)
    (Ty.subst_identity codomainType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) applyARaw]
      exact RawTerm.subst_identity applyARaw)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) applyBRaw]
      exact RawTerm.subst_identity applyBRaw)

/-- Univalence beta extraction case for ordinary identity substitution. -/
theorem Term.subst_identity_uaToEquiv_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (proof :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofHEq :
      HEq (Term.subst (TermSubst.identity context) proof) proof) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
          leftTyRaw rightTyRaw proof))
      (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
        leftTyRaw rightTyRaw proof) := by
  simp only [Term.subst]
  exact Term.uaToEquiv_HEq_congr
    (Ty.subst_identity leftTy)
    (Ty.subst_identity rightTy)
    (RawTerm.subst_identity leftTyRaw)
    (RawTerm.subst_identity rightTyRaw)
    (RawTerm.subst_identity proofRaw)
    proofHEq

end LeanFX2
