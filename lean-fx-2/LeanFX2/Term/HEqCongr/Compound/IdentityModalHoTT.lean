import LeanFX2.Term

/-! # Term/HEqCongr/Compound/IdentityModalHoTT

HEq congruence lemmas for identity, modal, universe-cumulativity, and
HoTT-special compound `Term` constructors. -/

namespace LeanFX2

/-- HEq congruence for `Term.refl`.  Both arguments (carrier type and
raw witness) are explicit.  This is unique among Term ctors because
the type Ty.id depends on the rawWitness in two positions
(left and right endpoint). -/
theorem Term.refl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    {rawWitness1 rawWitness2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (rawWitnessEq : rawWitness1 = rawWitness2) :
    HEq (Term.refl (context := context) carrier1 rawWitness1)
        (Term.refl (context := context) carrier2 rawWitness2) := by
  subst carrierEq
  subst rawWitnessEq
  rfl

/-- HEq congruence for `Term.idJ`. -/
theorem Term.idJ_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {motiveType1 motiveType2 : Ty level scope}
    {baseRaw1 baseRaw2 witnessRaw1 witnessRaw2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (leftEq : leftEndpoint1 = leftEndpoint2)
    (rightEq : rightEndpoint1 = rightEndpoint2)
    (motiveEq : motiveType1 = motiveType2)
    (baseRawEq : baseRaw1 = baseRaw2)
    (witnessRawEq : witnessRaw1 = witnessRaw2)
    {baseCase1 : Term context motiveType1 baseRaw1}
    {baseCase2 : Term context motiveType2 baseRaw2}
    (baseCaseHEq : HEq baseCase1 baseCase2)
    {witness1 : Term context (Ty.id carrier1 leftEndpoint1 rightEndpoint1) witnessRaw1}
    {witness2 : Term context (Ty.id carrier2 leftEndpoint2 rightEndpoint2) witnessRaw2}
    (witnessHEq : HEq witness1 witness2) :
    HEq (Term.idJ baseCase1 witness1) (Term.idJ baseCase2 witness2) := by
  subst carrierEq
  subst leftEq
  subst rightEq
  subst motiveEq
  subst baseRawEq
  subst witnessRawEq
  cases baseCaseHEq
  cases witnessHEq
  rfl

/-- HEq congruence for `Term.oeqRefl`. -/
theorem Term.oeqRefl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    {rawWitness1 rawWitness2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (rawWitnessEq : rawWitness1 = rawWitness2) :
    HEq (Term.oeqRefl (context := context) carrier1 rawWitness1)
      (Term.oeqRefl (context := context) carrier2 rawWitness2) := by
  subst carrierEq
  subst rawWitnessEq
  rfl

/-- HEq congruence for `Term.oeqJ`. -/
theorem Term.oeqJ_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {motiveType1 motiveType2 : Ty level scope}
    {baseRaw1 baseRaw2 witnessRaw1 witnessRaw2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (leftEq : leftEndpoint1 = leftEndpoint2)
    (rightEq : rightEndpoint1 = rightEndpoint2)
    (motiveEq : motiveType1 = motiveType2)
    (baseRawEq : baseRaw1 = baseRaw2)
    (witnessRawEq : witnessRaw1 = witnessRaw2)
    {baseCase1 : Term context motiveType1 baseRaw1}
    {baseCase2 : Term context motiveType2 baseRaw2}
    (baseCaseHEq : HEq baseCase1 baseCase2)
    {witness1 :
      Term context (Ty.oeq carrier1 leftEndpoint1 rightEndpoint1) witnessRaw1}
    {witness2 :
      Term context (Ty.oeq carrier2 leftEndpoint2 rightEndpoint2) witnessRaw2}
    (witnessHEq : HEq witness1 witness2) :
    HEq (Term.oeqJ baseCase1 witness1) (Term.oeqJ baseCase2 witness2) := by
  subst carrierEq
  subst leftEq
  subst rightEq
  subst motiveEq
  subst baseRawEq
  subst witnessRawEq
  cases baseCaseHEq
  cases witnessHEq
  rfl

/-- HEq congruence for observational funext. -/
theorem Term.oeqFunext_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {leftFunctionRaw1 leftFunctionRaw2 rightFunctionRaw1 rightFunctionRaw2 :
      RawTerm scope}
    {pointwiseRaw1 pointwiseRaw2 : RawTerm scope}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (leftFunctionRawEq : leftFunctionRaw1 = leftFunctionRaw2)
    (rightFunctionRawEq : rightFunctionRaw1 = rightFunctionRaw2)
    (pointwiseRawEq : pointwiseRaw1 = pointwiseRaw2)
    {pointwiseProof1 :
      Term context
        (oeqFunextPointwiseType domainType1 codomainType1
          leftFunctionRaw1 rightFunctionRaw1)
        pointwiseRaw1}
    {pointwiseProof2 :
      Term context
        (oeqFunextPointwiseType domainType2 codomainType2
          leftFunctionRaw2 rightFunctionRaw2)
        pointwiseRaw2}
    (pointwiseProofHEq : HEq pointwiseProof1 pointwiseProof2) :
    HEq
      (Term.oeqFunext domainType1 codomainType1 leftFunctionRaw1
        rightFunctionRaw1 pointwiseProof1)
      (Term.oeqFunext domainType2 codomainType2 leftFunctionRaw2
        rightFunctionRaw2 pointwiseProof2) := by
  subst domainEq
  subst codomainEq
  subst leftFunctionRawEq
  subst rightFunctionRawEq
  subst pointwiseRawEq
  cases pointwiseProofHEq
  rfl

/-- HEq congruence for strict identity reflexivity with shared strictness
evidence. -/
theorem Term.idStrictRefl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier1 carrier2 : Ty level scope}
    {rawWitness1 rawWitness2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (rawWitnessEq : rawWitness1 = rawWitness2) :
    HEq
      (Term.idStrictRefl (context := context) modeIsStrict carrier1
        rawWitness1)
      (Term.idStrictRefl (context := context) modeIsStrict carrier2
        rawWitness2) := by
  subst carrierEq
  subst rawWitnessEq
  rfl

/-- HEq congruence for strict identity recursion with shared strictness
evidence. -/
theorem Term.idStrictRec_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier1 carrier2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {motiveType1 motiveType2 : Ty level scope}
    {baseRaw1 baseRaw2 witnessRaw1 witnessRaw2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (leftEq : leftEndpoint1 = leftEndpoint2)
    (rightEq : rightEndpoint1 = rightEndpoint2)
    (motiveEq : motiveType1 = motiveType2)
    (baseRawEq : baseRaw1 = baseRaw2)
    (witnessRawEq : witnessRaw1 = witnessRaw2)
    {baseCase1 : Term context motiveType1 baseRaw1}
    {baseCase2 : Term context motiveType2 baseRaw2}
    (baseCaseHEq : HEq baseCase1 baseCase2)
    {witness1 :
      Term context (Ty.idStrict carrier1 leftEndpoint1 rightEndpoint1)
        witnessRaw1}
    {witness2 :
      Term context (Ty.idStrict carrier2 leftEndpoint2 rightEndpoint2)
        witnessRaw2}
    (witnessHEq : HEq witness1 witness2) :
    HEq (Term.idStrictRec modeIsStrict baseCase1 witness1)
      (Term.idStrictRec modeIsStrict baseCase2 witness2) := by
  subst carrierEq
  subst leftEq
  subst rightEq
  subst motiveEq
  subst baseRawEq
  subst witnessRawEq
  cases baseCaseHEq
  cases witnessHEq
  rfl

/-- HEq congruence for `Term.modIntro`. -/
theorem Term.modIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType1 innerType2 : Ty level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerTypeEq : innerType1 = innerType2)
    (innerRawEq : innerRaw1 = innerRaw2)
    {inner1 : Term context innerType1 innerRaw1}
    {inner2 : Term context innerType2 innerRaw2}
    (innerHEq : HEq inner1 inner2) :
    HEq (Term.modIntro inner1) (Term.modIntro inner2) := by
  subst innerTypeEq
  subst innerRawEq
  cases innerHEq
  rfl

/-- HEq congruence for `Term.modElim`. -/
theorem Term.modElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType1 innerType2 : Ty level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerTypeEq : innerType1 = innerType2)
    (innerRawEq : innerRaw1 = innerRaw2)
    {inner1 : Term context innerType1 innerRaw1}
    {inner2 : Term context innerType2 innerRaw2}
    (innerHEq : HEq inner1 inner2) :
    HEq (Term.modElim inner1) (Term.modElim inner2) := by
  subst innerTypeEq
  subst innerRawEq
  cases innerHEq
  rfl

/-- HEq congruence for `Term.subsume`. -/
theorem Term.subsume_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerType1 innerType2 : Ty level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerTypeEq : innerType1 = innerType2)
    (innerRawEq : innerRaw1 = innerRaw2)
    {inner1 : Term context innerType1 innerRaw1}
    {inner2 : Term context innerType2 innerRaw2}
    (innerHEq : HEq inner1 inner2) :
    HEq (Term.subsume inner1) (Term.subsume inner2) := by
  subst innerTypeEq
  subst innerRawEq
  cases innerHEq
  rfl

/-- HEq congruence for `Term.cumulUp`. -/
theorem Term.cumulUp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {lowerLevel higherLevel : UniverseLevel}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {levelLeLow : lowerLevel.toNat + 1 ≤ level}
    {levelLeHigh : higherLevel.toNat + 1 ≤ level}
    {codeRaw1 codeRaw2 : RawTerm scope}
    (codeRawEq : codeRaw1 = codeRaw2)
    {typeCode1 : Term context (Ty.universe lowerLevel levelLeLow) codeRaw1}
    {typeCode2 : Term context (Ty.universe lowerLevel levelLeLow) codeRaw2}
    (typeCodeHEq : HEq typeCode1 typeCode2) :
    HEq
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode1)
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode2) := by
  subst codeRawEq
  cases typeCodeHEq
  rfl

/-- HEq congruence for the canonical identity equivalence. -/
theorem Term.equivReflId_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrier1 carrier2 : Ty level scope}
    (carrierEq : carrier1 = carrier2) :
    HEq (Term.equivReflId (context := context) carrier1)
      (Term.equivReflId (context := context) carrier2) := by
  subst carrierEq
  rfl

/-- HEq congruence for canonical funext reflexivity. -/
theorem Term.funextRefl_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {applyRaw1 applyRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (applyRawEq : applyRaw1 = applyRaw2) :
    HEq
      (Term.funextRefl (context := context) domainType1 codomainType1
        applyRaw1)
      (Term.funextRefl (context := context) domainType2 codomainType2
        applyRaw2) := by
  subst domainEq
  subst codomainEq
  subst applyRawEq
  rfl

/-- HEq congruence for the Id-typed identity-equivalence witness. -/
theorem Term.equivReflIdAtId_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerLevel : UniverseLevel}
    {innerLevelLt : innerLevel.toNat + 1 ≤ level}
    {carrier1 carrier2 : Ty level scope}
    {carrierRaw1 carrierRaw2 : RawTerm scope}
    (carrierEq : carrier1 = carrier2)
    (carrierRawEq : carrierRaw1 = carrierRaw2) :
    HEq
      (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
        carrier1 carrierRaw1)
      (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
        carrier2 carrierRaw2) := by
  subst carrierEq
  subst carrierRawEq
  rfl

/-- HEq congruence for the Id-typed funext witness. -/
theorem Term.funextReflAtId_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {applyRaw1 applyRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (applyRawEq : applyRaw1 = applyRaw2) :
    HEq
      (Term.funextReflAtId (context := context) domainType1 codomainType1
        applyRaw1)
      (Term.funextReflAtId (context := context) domainType2 codomainType2
        applyRaw2) := by
  subst domainEq
  subst codomainEq
  subst applyRawEq
  rfl

/-- HEq congruence for univalence beta extraction. -/
theorem Term.uaToEquiv_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerLevel : UniverseLevel}
    {innerLevelLt : innerLevel.toNat + 1 ≤ level}
    {leftTy1 leftTy2 rightTy1 rightTy2 : Ty level scope}
    {leftTyRaw1 leftTyRaw2 rightTyRaw1 rightTyRaw2 proofRaw1 proofRaw2 :
      RawTerm scope}
    (leftTyEq : leftTy1 = leftTy2)
    (rightTyEq : rightTy1 = rightTy2)
    (leftTyRawEq : leftTyRaw1 = leftTyRaw2)
    (rightTyRawEq : rightTyRaw1 = rightTyRaw2)
    (proofRawEq : proofRaw1 = proofRaw2)
    {proof1 :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw1 rightTyRaw1)
        proofRaw1}
    {proof2 :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw2 rightTyRaw2)
        proofRaw2}
    (proofHEq : HEq proof1 proof2) :
    HEq
      (Term.uaToEquiv innerLevel innerLevelLt leftTy1 rightTy1
        leftTyRaw1 rightTyRaw1 proof1)
      (Term.uaToEquiv innerLevel innerLevelLt leftTy2 rightTy2
        leftTyRaw2 rightTyRaw2 proof2) := by
  subst leftTyEq
  subst rightTyEq
  subst leftTyRawEq
  subst rightTyRawEq
  subst proofRawEq
  cases proofHEq
  rfl

/-- HEq congruence for univalence beta application. -/
theorem Term.equivApply_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {equivRaw1 equivRaw2 argumentRaw1 argumentRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (equivRawEq : equivRaw1 = equivRaw2)
    (argumentRawEq : argumentRaw1 = argumentRaw2)
    {equivTerm1 : Term context (Ty.equiv carrierA1 carrierB1) equivRaw1}
    {equivTerm2 : Term context (Ty.equiv carrierA2 carrierB2) equivRaw2}
    (equivHEq : HEq equivTerm1 equivTerm2)
    {argumentTerm1 : Term context carrierA1 argumentRaw1}
    {argumentTerm2 : Term context carrierA2 argumentRaw2}
    (argumentHEq : HEq argumentTerm1 argumentTerm2) :
    HEq (Term.equivApply equivTerm1 argumentTerm1)
      (Term.equivApply equivTerm2 argumentTerm2) := by
  subst carrierAEq
  subst carrierBEq
  subst equivRawEq
  subst argumentRawEq
  cases equivHEq
  cases argumentHEq
  rfl

end LeanFX2
