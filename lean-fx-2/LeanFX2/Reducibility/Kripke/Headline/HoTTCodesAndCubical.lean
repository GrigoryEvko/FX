import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.Fundamental
import LeanFX2.Reducibility.Kripke.Arrow
import LeanFX2.Reducibility.Kripke.SNExtraction

/-! # LeanFX2.Reducibility.Kripke.Headline.HoTTCodesAndCubical

Kripke-derived strong-normalization headlines for type-code, HoTT,
equivalence, cubical, and effect constructors whose wrappers are direct
from the underlying SN lemmas.
-/

namespace LeanFX2

/-- SN of equivReflId via Kripke. -/
theorem Term.equivReflId_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope) :
    Term.isStronglyNormalizing
      (Term.equivReflId (context := sourceCtx) carrier) :=
  Term.equivReflId_isStronglyNormalizing carrier

/-- SN of uaToEquiv via Kripke. -/
theorem Term.uaToEquiv_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    {proof :
        Term sourceCtx
          (Ty.id (Ty.universe innerLevel innerLevelLt)
            leftTyRaw rightTyRaw)
          proofRaw}
    (proofIsSN : Term.isStronglyNormalizing proof) :
    Term.isStronglyNormalizing
      (Term.uaToEquiv innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) :=
  Term.uaToEquiv_isStronglyNormalizing innerLevel innerLevelLt
    leftTy rightTy leftTyRaw rightTyRaw proofIsSN

/-- SN of arrowCode via Kripke. -/
theorem Term.arrowCode_strong_normalization_via_kripke
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
  Term.arrowCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

/-- SN of eitherCode via Kripke. -/
theorem Term.eitherCode_strong_normalization_via_kripke
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
  Term.eitherCode_isStronglyNormalizing outerLevel levelLe
    leftCodeIsSN rightCodeIsSN

/-- SN of equivCode via Kripke. -/
theorem Term.equivCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsSN : RawTerm.isStronglyNormalizing leftTypeCodeRaw)
    (rightTypeCodeIsSN : RawTerm.isStronglyNormalizing rightTypeCodeRaw) :
    Term.isStronglyNormalizing
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) :=
  Term.equivCode_isStronglyNormalizing outerLevel levelLe
    leftTypeCodeIsSN rightTypeCodeIsSN

/-- SN of listCode via Kripke. -/
theorem Term.listCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Term.listCode_isStronglyNormalizing outerLevel levelLe elementCodeIsSN

/-- SN of optionCode via Kripke. -/
theorem Term.optionCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Term.optionCode_isStronglyNormalizing outerLevel levelLe elementCodeIsSN

/-- SN of idCode via Kripke. -/
theorem Term.idCode_strong_normalization_via_kripke
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
  Term.idCode_isStronglyNormalizing outerLevel levelLe
    typeCodeIsSN leftIsSN rightIsSN

/-- SN of pathLam via Kripke (univalent mode). -/
theorem Term.pathLam_strong_normalization_via_kripke
    {level scope : Nat}
    {context : Ctx Mode.univalent level scope}
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
        Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing
      (Term.pathLam rfl carrierType leftEndpoint rightEndpoint bodyTerm) :=
  Term.pathLam_isStronglyNormalizing rfl carrierType
    leftEndpoint rightEndpoint bodyIsSN

/-- SN of glueIntro via Kripke (univalent mode). -/
theorem Term.glueIntro_strong_normalization_via_kripke
    {level scope : Nat}
    {context : Ctx Mode.univalent level scope}
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIsSN : Term.isStronglyNormalizing baseValue)
    (partialIsSN : Term.isStronglyNormalizing partialValue) :
    Term.isStronglyNormalizing
      (Term.glueIntro rfl baseType boundaryWitness baseValue partialValue) :=
  Term.glueIntro_isStronglyNormalizing rfl baseType boundaryWitness
    baseIsSN partialIsSN

/-- SN of glueElim via Kripke (univalent mode). -/
theorem Term.glueElim_strong_normalization_via_kripke
    {level scope : Nat}
    {context : Ctx Mode.univalent level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue :
        Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIsSN : Term.isStronglyNormalizing gluedValue) :
    Term.isStronglyNormalizing (Term.glueElim rfl gluedValue) :=
  Term.glueElim_isStronglyNormalizing rfl gluedIsSN

/-- SN of equivIntroHet via Kripke. -/
theorem Term.equivIntroHet_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
        Term context (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
        Term context (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
        Term context
          (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
          leftInvRaw}
    {rightInv :
        Term context
          (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
          rightInvRaw}
    (forwardIsSN : Term.isStronglyNormalizing forward)
    (backwardIsSN : Term.isStronglyNormalizing backward) :
    Term.isStronglyNormalizing
      (Term.equivIntroHet forward backward leftInv rightInv) :=
  Term.equivIntroHet_isStronglyNormalizing forwardIsSN backwardIsSN

/-- SN of funextRefl via Kripke. -/
theorem Term.funextRefl_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (applyIsSN : RawTerm.isStronglyNormalizing applyRaw) :
    Term.isStronglyNormalizing
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextRefl_isStronglyNormalizing_of_apply
    domainType codomainType applyIsSN

/-- SN of funextReflAtId via Kripke. -/
theorem Term.funextReflAtId_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (applyIsSN : RawTerm.isStronglyNormalizing applyRaw) :
    Term.isStronglyNormalizing
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextReflAtId_isStronglyNormalizing_of_apply
    domainType codomainType applyIsSN

/-- SN of oeqFunext via Kripke. -/
theorem Term.oeqFunext_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    {pointwiseProof :
        Term sourceCtx
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRaw}
    (pointwiseIsSN : Term.isStronglyNormalizing pointwiseProof) :
    Term.isStronglyNormalizing
      (Term.oeqFunext domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof) :=
  Term.oeqFunext_isStronglyNormalizing
    domainType codomainType leftFunctionRaw rightFunctionRaw pointwiseIsSN

/-- SN of effectPerform via Kripke. -/
theorem Term.effectPerform_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
        Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
        Term sourceCtx
          (Ty.effect operationSignature.argumentCarrier effectTag)
          operationRaw}
    {arguments :
        Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIsSN : Term.isStronglyNormalizing operationTag)
    (argumentsAreSN : Term.isStronglyNormalizing arguments) :
    Term.isStronglyNormalizing
      (Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments) :=
  Term.effectPerform_isStronglyNormalizing effectTag effectRow
    operationSignature canPerformOperation operationIsSN argumentsAreSN

/-- SN of uaIntroHet via Kripke. -/
theorem Term.uaIntroHet_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    {equivWitness :
        Term sourceCtx (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivWitnessIsSN : Term.isStronglyNormalizing equivWitness) :
    Term.isStronglyNormalizing
      (Term.uaIntroHet innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) :=
  Term.uaIntroHet_isStronglyNormalizing innerLevel innerLevelLt
    carrierARaw carrierBRaw equivWitnessIsSN

/-- SN of equivReflIdAtId via Kripke. -/
theorem Term.equivReflIdAtId_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Term.isStronglyNormalizing
      (Term.equivReflIdAtId (context := sourceCtx)
        innerLevel innerLevelLt carrier carrierRaw) :=
  Term.equivReflIdAtId_isStronglyNormalizing
    innerLevel innerLevelLt carrier carrierRaw

end LeanFX2
