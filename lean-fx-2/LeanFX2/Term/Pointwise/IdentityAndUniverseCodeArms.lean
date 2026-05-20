import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.HEqCongr.Atomic.TypeCodes
import LeanFX2.Term.Subst
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.LiftCompose

/-! # LeanFX2.Term.Pointwise.IdentityAndUniverseCodeArms

weaken-subst-singleton arms for the identity/observational equality
family (refl, idJ, oeqRefl, oeqJ, oeqFunext, idStrictRefl, idStrictRec)
and the universe-code family (universeCode, arrowCode, piTyCode,
sigmaTyCode, productCode, sumCode, listCode, optionCode, eitherCode,
idCode, equivCode, equivReflId, equivReflIdAtId).

## Root status

Kernel — identity and universe-code arms of the Pointwise
weaken-then-singleton cascade. -/

namespace LeanFX2

/-- Identity reflexivity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_refl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.refl (context := context) carrier rawWitness)))
      (Term.refl (context := context) carrier rawWitness) :=
  -- `Term.subst _ (Term.weaken _ (Term.refl ..))` reduces by iota (the
  -- clean `.refl` rename/subst arms push the operations onto the carrier
  -- and witness with no cast), so the congruence closes through
  -- definitional equality without generating the 78-arm `Term.subst` /
  -- `Term.rename` equational unfolder that the kernel must re-check.
  Term.refl_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton rawWitness singletonRaw)

/-- Identity elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idJ_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseCase))
        baseCase)
    (witnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType witness))
        witness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.idJ baseCase witness)))
      (Term.idJ baseCase witness) :=
  -- The `.idJ` rename/subst arms recurse structurally with no cast, so
  -- the congruence closes through iota reduction; dropping `simp only`
  -- avoids materializing the 78-arm equational unfolder for the kernel
  -- to re-check.
  Term.idJ_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton witnessRaw singletonRaw)
    baseCaseHEq witnessHEq

/-- Observational reflexivity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_oeqRefl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.oeqRefl (context := context) carrier rawWitness)))
      (Term.oeqRefl (context := context) carrier rawWitness) :=
  -- The clean `.oeqRefl` rename/subst arms push the operations onto the
  -- carrier and witness with no cast, so the congruence closes through
  -- iota reduction without the 78-arm equational unfolder.
  Term.oeqRefl_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton rawWitness singletonRaw)

/-- Observational equality elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_oeqJ_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw)
    (baseCaseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseCase))
        baseCase)
    (witnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType witness))
        witness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.oeqJ baseCase witness)))
      (Term.oeqJ baseCase witness) :=
  -- The `.oeqJ` rename/subst arms recurse structurally with no cast, so
  -- the congruence closes through iota reduction; dropping `simp only`
  -- avoids materializing the 78-arm equational unfolder.
  Term.oeqJ_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton witnessRaw singletonRaw)
    baseCaseHEq witnessHEq

/-- Observational funext preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_oeqFunext_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {leftFunctionRaw rightFunctionRaw pointwiseRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (pointwiseProof :
      Term context
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw)
    (pointwiseProofHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType pointwiseProof))
        pointwiseProof) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.oeqFunext domainType codomainType leftFunctionRaw
            rightFunctionRaw pointwiseProof)))
      (Term.oeqFunext domainType codomainType leftFunctionRaw
        rightFunctionRaw pointwiseProof) := by
  -- The `.oeqFunext` rename/subst arms carry a `▸` transport on the
  -- pointwise proof (`oeqFunextPointwiseType_{rename,subst}`); the cast
  -- chain below reconstructs exactly that transported shape, so the
  -- final congruence closes through iota reduction without the slow
  -- `simp only [Term.weaken, Term.rename, Term.subst]` 78-arm unfolder.
  let renamedPointwiseProof :=
    Term.rename (TermRenaming.weakenStep context newType) pointwiseProof
  let renamedPointwiseTypeEq :=
    oeqFunextPointwiseType_rename RawRenaming.weaken domainType
      codomainType leftFunctionRaw rightFunctionRaw
  let substitutedPointwiseProofWithCast :=
    Term.subst (TermSubst.singleton singletonTerm)
      (renamedPointwiseTypeEq ▸ renamedPointwiseProof)
  let substitutedPointwiseTypeEq :=
    oeqFunextPointwiseType_subst (Subst.singleton newType singletonRaw)
      (domainType.rename RawRenaming.weaken)
      (codomainType.rename RawRenaming.weaken)
      (leftFunctionRaw.rename RawRenaming.weaken)
      (rightFunctionRaw.rename RawRenaming.weaken)
  have pointwiseInnerCastHEq :
      HEq substitutedPointwiseProofWithCast
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedPointwiseProof) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      renamedPointwiseTypeEq
      renamedPointwiseProof
  have pointwiseOuterCastHEq :
      HEq (substitutedPointwiseTypeEq ▸ substitutedPointwiseProofWithCast)
        substitutedPointwiseProofWithCast :=
    Term.type_eq_cast_heq substitutedPointwiseTypeEq
      substitutedPointwiseProofWithCast
  have pointwiseWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedPointwiseProof)
        pointwiseProof := by
    simpa only [Term.weaken] using pointwiseProofHEq
  have pointwiseFullHEq :
      HEq (substitutedPointwiseTypeEq ▸ substitutedPointwiseProofWithCast)
        pointwiseProof :=
    HEq.trans pointwiseOuterCastHEq
      (HEq.trans pointwiseInnerCastHEq pointwiseWithoutCastsHEq)
  exact Term.oeqFunext_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftFunctionRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightFunctionRaw singletonRaw)
    (RawTerm.weaken_subst_singleton pointwiseRaw singletonRaw)
    pointwiseFullHEq

/-- Strict identity reflexivity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idStrictRefl_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.idStrictRefl (context := context) modeIsStrict carrier
            rawWitness)))
      (Term.idStrictRefl (context := context) modeIsStrict carrier
        rawWitness) :=
  -- The clean `.idStrictRefl` rename/subst arms push the operations onto
  -- the carrier and witness with no cast, so the congruence closes
  -- through iota reduction without the 78-arm equational unfolder.
  Term.idStrictRefl_HEq_congr modeIsStrict
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton rawWitness singletonRaw)

/-- Strict identity recursion preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idStrictRec_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw)
    (baseCaseHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType baseCase))
        baseCase)
    (witnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType witness))
        witness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.idStrictRec modeIsStrict baseCase witness)))
      (Term.idStrictRec modeIsStrict baseCase witness) :=
  -- The `.idStrictRec` rename/subst arms recurse structurally with no
  -- cast, so the congruence closes through iota reduction; dropping
  -- `simp only` avoids materializing the 78-arm equational unfolder.
  Term.idStrictRec_HEq_congr modeIsStrict
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (Ty.weaken_subst_singleton motiveType newType singletonRaw)
    (RawTerm.weaken_subst_singleton baseRaw singletonRaw)
    (RawTerm.weaken_subst_singleton witnessRaw singletonRaw)
    baseCaseHEq witnessHEq

/-- Universe-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_universeCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.universeCode (context := context) innerLevel outerLevel
            cumulOk levelLe)))
      (Term.universeCode (context := context) innerLevel outerLevel
        cumulOk levelLe) :=
  -- The `.universeCode` rename/subst arms return the constructor
  -- unchanged, so the congruence closes through iota reduction without
  -- the 78-arm equational unfolder.
  Term.universeCode_HEq_congr innerLevel outerLevel cumulOk levelLe

/-- Arrow type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_arrowCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.arrowCode (context := context) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)))
      (Term.arrowCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) :=
  -- The `.arrowCode` rename/subst arms push the operations onto the
  -- domain and codomain codes with no cast, so the congruence closes
  -- through iota reduction without the 78-arm equational unfolder.
  Term.arrowCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton domainCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton codomainCodeRaw singletonRaw)

/-- Pi type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_piTyCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.piTyCode (context := context) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)))
      (Term.piTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) :=
  -- The `.piTyCode` rename/subst arms push the operations onto the
  -- domain code and (lifted) codomain code with no cast, so the
  -- congruence closes through iota reduction without the 78-arm
  -- equational unfolder.
  Term.piTyCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton domainCodeRaw singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift codomainCodeRaw singletonRaw)

/-- Sigma type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sigmaTyCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.sigmaTyCode (context := context) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)))
      (Term.sigmaTyCode (context := context) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) :=
  -- The `.sigmaTyCode` rename/subst arms push the operations onto the
  -- domain code and (lifted) codomain code with no cast, so the
  -- congruence closes through iota reduction without the 78-arm
  -- equational unfolder.
  Term.sigmaTyCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton domainCodeRaw singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift codomainCodeRaw singletonRaw)

/-- Product type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_productCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.productCode (context := context) outerLevel levelLe
            firstCodeRaw secondCodeRaw)))
      (Term.productCode (context := context) outerLevel levelLe
        firstCodeRaw secondCodeRaw) :=
  -- The `.productCode` rename/subst arms push the operations onto the
  -- first and second codes with no cast, so the congruence closes
  -- through iota reduction without the 78-arm equational unfolder.
  Term.productCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton firstCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton secondCodeRaw singletonRaw)

/-- Sum type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_sumCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.sumCode (context := context) outerLevel levelLe
            leftCodeRaw rightCodeRaw)))
      (Term.sumCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) :=
  -- The `.sumCode` rename/subst arms push the operations onto the left
  -- and right codes with no cast, so the congruence closes through iota
  -- reduction without the 78-arm equational unfolder.
  Term.sumCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton leftCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightCodeRaw singletonRaw)

/-- List type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_listCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.listCode (context := context) outerLevel levelLe
            elementCodeRaw)))
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw) :=
  -- The `.listCode` rename/subst arms push the operation onto the
  -- element code with no cast, so the congruence closes through iota
  -- reduction without the 78-arm equational unfolder.
  Term.listCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton elementCodeRaw singletonRaw)

/-- Option type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_optionCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.optionCode (context := context) outerLevel levelLe
            elementCodeRaw)))
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw) :=
  -- The `.optionCode` rename/subst arms push the operation onto the
  -- element code with no cast, so the congruence closes through iota
  -- reduction without the 78-arm equational unfolder.
  Term.optionCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton elementCodeRaw singletonRaw)

/-- Either type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_eitherCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.eitherCode (context := context) outerLevel levelLe
            leftCodeRaw rightCodeRaw)))
      (Term.eitherCode (context := context) outerLevel levelLe
        leftCodeRaw rightCodeRaw) :=
  -- The `.eitherCode` rename/subst arms push the operations onto the
  -- left and right codes with no cast, so the congruence closes through
  -- iota reduction without the 78-arm equational unfolder.
  Term.eitherCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton leftCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightCodeRaw singletonRaw)

/-- Identity type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_idCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.idCode (context := context) outerLevel levelLe typeCodeRaw
            leftRaw rightRaw)))
      (Term.idCode (context := context) outerLevel levelLe typeCodeRaw
        leftRaw rightRaw) :=
  -- The `.idCode` rename/subst arms push the operations onto the type
  -- code and the two endpoint codes with no cast, so the congruence
  -- closes through iota reduction without the 78-arm equational
  -- unfolder.
  Term.idCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton typeCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton leftRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightRaw singletonRaw)

/-- Equivalence type-code values preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivCode_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.equivCode (context := context) outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw)))
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) :=
  -- The `.equivCode` rename/subst arms push the operations onto the two
  -- type codes with no cast, so the congruence closes through iota
  -- reduction without the 78-arm equational unfolder.
  Term.equivCode_HEq_congr outerLevel levelLe
    (RawTerm.weaken_subst_singleton leftTypeCodeRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightTypeCodeRaw singletonRaw)

/-- Canonical identity equivalences preserve weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivReflId_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.equivReflId (context := context) carrier)))
      (Term.equivReflId (context := context) carrier) :=
  -- The `.equivReflId` rename/subst arms push the operation onto the
  -- carrier with no cast, so the congruence closes through iota
  -- reduction without the 78-arm equational unfolder.
  Term.equivReflId_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)

/-- Id-typed identity equivalence witnesses preserve weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_equivReflIdAtId_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope)
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
            carrier carrierRaw)))
      (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
        carrier carrierRaw) :=
  -- The `.equivReflIdAtId` rename/subst arms push the operations onto
  -- the carrier and witness with no cast, so the congruence closes
  -- through iota reduction without the 78-arm equational unfolder.
  Term.equivReflIdAtId_HEq_congr
    (Ty.weaken_subst_singleton carrier newType singletonRaw)
    (RawTerm.weaken_subst_singleton carrierRaw singletonRaw)

end LeanFX2
