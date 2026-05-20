import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.Structural
import LeanFX2.Term.HEqCongr.Atomic.HeterogeneousIntro
import LeanFX2.Term.Subst
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.LiftCompose

/-! # LeanFX2.Term.Pointwise.EffectAndHoTTHetArms

weaken-subst-singleton arms for the effect family (direct + read-via-write
carrier congruence helpers, effectPerform) and the heterogeneous HoTT
family (uaToEquiv, pathApp, glueElim, recordProj, codataDest,
equivIntroHet, equivApp, equivApply, uaIntroHet, funextIntroHet, cumulUp).
Also ships the trailing cast-aware HEq scaffolding section for
Term.subst_compose.

## Root status

Kernel — effect and heterogeneous HoTT arms of the Pointwise
weaken-then-singleton cascade. -/

namespace LeanFX2

/-- Direct effect-performance congruence with propositionally equal
operation carriers. -/
private theorem Term.effectPerform_direct_carrier_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (effectLabel : Effects.EffectLabel)
    (rowMember : Effects.EffectRow.Member effectLabel effectRow)
    {argumentCarrier1 argumentCarrier2 resultCarrier1 resultCarrier2 :
      Ty level scope}
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 :
      RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (argumentCarrierEq : argumentCarrier1 = argumentCarrier2)
    (resultCarrierEq : resultCarrier1 = resultCarrier2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context (Ty.effect argumentCarrier1 effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context (Ty.effect argumentCarrier2 effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 : Term context argumentCarrier1 argumentsRaw1}
    {arguments2 : Term context argumentCarrier2 argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow
        { effectLabel := effectLabel
          argumentCarrier := argumentCarrier1
          resultCarrier := resultCarrier1 }
        (Effects.CanPerform.direct rowMember) operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow
        { effectLabel := effectLabel
          argumentCarrier := argumentCarrier2
          resultCarrier := resultCarrier2 }
        (Effects.CanPerform.direct rowMember) operationTag2 arguments2) := by
  subst effectTagEq
  subst argumentCarrierEq
  subst resultCarrierEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

/-- Read-via-write effect-performance congruence with propositionally
equal operation carriers. -/
private theorem Term.effectPerform_readViaWrite_carrier_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (rowMember : Effects.EffectRow.Member Effects.EffectLabel.write
      effectRow)
    {argumentCarrier1 argumentCarrier2 resultCarrier1 resultCarrier2 :
      Ty level scope}
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 :
      RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (argumentCarrierEq : argumentCarrier1 = argumentCarrier2)
    (resultCarrierEq : resultCarrier1 = resultCarrier2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context (Ty.effect argumentCarrier1 effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context (Ty.effect argumentCarrier2 effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 : Term context argumentCarrier1 argumentsRaw1}
    {arguments2 : Term context argumentCarrier2 argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier := argumentCarrier1
          resultCarrier := resultCarrier1 }
        (Effects.CanPerform.readViaWrite argumentCarrier1
          resultCarrier1 rowMember)
        operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier := argumentCarrier2
          resultCarrier := resultCarrier2 }
        (Effects.CanPerform.readViaWrite argumentCarrier2
          resultCarrier2 rowMember)
        operationTag2 arguments2) := by
  subst effectTagEq
  subst argumentCarrierEq
  subst resultCarrierEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

/-- Effect performance preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_effectPerform_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {effectTag : RawTerm scope}
    {effectRow : Effects.EffectRow}
    {operationSignature : Effects.OperationSignature (Ty level scope)}
    {canPerformOperation :
      Effects.CanPerform effectRow operationSignature}
    {operationRaw argumentsRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (operationTag :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw)
    (operationTagHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType operationTag))
        operationTag)
    (argumentsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType arguments))
        arguments) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.effectPerform effectTag effectRow operationSignature
            canPerformOperation operationTag arguments)))
      (Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments) := by
  have operationTagWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            operationTag))
        operationTag := by
    simpa only [Term.weaken] using operationTagHEq
  have argumentsWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.rename (TermRenaming.weakenStep context newType)
            arguments))
        arguments := by
    simpa only [Term.weaken] using argumentsHEq
  cases operationSignature with
  | mk effectLabel argumentCarrier resultCarrier =>
    cases canPerformOperation with
    | direct rowMember =>
      exact Term.effectPerform_direct_carrier_HEq_congr
        effectRow effectLabel rowMember
        (RawTerm.weaken_subst_singleton effectTag singletonRaw)
        (Ty.weaken_subst_singleton argumentCarrier newType singletonRaw)
        (Ty.weaken_subst_singleton resultCarrier newType singletonRaw)
        (RawTerm.weaken_subst_singleton operationRaw singletonRaw)
        (RawTerm.weaken_subst_singleton argumentsRaw singletonRaw)
        operationTagWithoutCastsHEq
        argumentsWithoutCastsHEq
    | readViaWrite argumentCarrier resultCarrier rowMember =>
      exact Term.effectPerform_readViaWrite_carrier_HEq_congr
        effectRow rowMember
        (RawTerm.weaken_subst_singleton effectTag singletonRaw)
        (Ty.weaken_subst_singleton argumentCarrier newType singletonRaw)
        (Ty.weaken_subst_singleton resultCarrier newType singletonRaw)
        (RawTerm.weaken_subst_singleton operationRaw singletonRaw)
        (RawTerm.weaken_subst_singleton argumentsRaw singletonRaw)
        operationTagWithoutCastsHEq
        argumentsWithoutCastsHEq

/-- Univalence-to-equivalence extraction preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_uaToEquiv_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (proof :
      Term context
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType proof))
        proof) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw
            rightTyRaw proof)))
      (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw
        rightTyRaw proof) := by
  exact Term.uaToEquiv_HEq_congr
    (Ty.weaken_subst_singleton leftTy newType singletonRaw)
    (Ty.weaken_subst_singleton rightTy newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftTyRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightTyRaw singletonRaw)
    (RawTerm.weaken_subst_singleton proofRaw singletonRaw)
    proofHEq

/-- Path application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_pathApp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint pathRaw intervalRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType pathTerm))
        pathTerm)
    (intervalHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType intervalTerm))
        intervalTerm) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.pathApp modeIsUnivalent pathTerm intervalTerm)))
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  exact Term.pathApp_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton carrierType newType singletonRaw)
    (RawTerm.weaken_subst_singleton leftEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton rightEndpoint singletonRaw)
    (RawTerm.weaken_subst_singleton pathRaw singletonRaw)
    (RawTerm.weaken_subst_singleton intervalRaw singletonRaw)
    pathHEq intervalHEq

/-- Glue elimination preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_glueElim_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType gluedValue))
        gluedValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.glueElim modeIsUnivalent gluedValue)))
      (Term.glueElim modeIsUnivalent gluedValue) := by
  exact Term.glueElim_HEq_congr modeIsUnivalent
    (Ty.weaken_subst_singleton baseType newType singletonRaw)
    (RawTerm.weaken_subst_singleton boundaryWitness singletonRaw)
    (RawTerm.weaken_subst_singleton gluedRaw singletonRaw)
    gluedHEq

/-- Record projection preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_recordProj_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType recordValue))
        recordValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.recordProj recordValue)))
      (Term.recordProj recordValue) := by
  exact Term.recordProj_HEq_congr
    (Ty.weaken_subst_singleton singleFieldType newType singletonRaw)
    (RawTerm.weaken_subst_singleton recordRaw singletonRaw)
    recordHEq

/-- Codata destruction preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_codataDest_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType codataValue))
        codataValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.codataDest codataValue)))
      (Term.codataDest codataValue) := by
  exact Term.codataDest_HEq_congr
    (Ty.weaken_subst_singleton stateType newType singletonRaw)
    (Ty.weaken_subst_singleton outputType newType singletonRaw)
    (RawTerm.weaken_subst_singleton codataRaw singletonRaw)
    codataHEq

/-- Heterogeneous equivalence introduction preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_equivIntroHet_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (forward :
      Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward :
      Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv :
      Term context
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInv :
      Term context
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw)
    (forwardHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType forward))
        forward)
    (backwardHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType backward))
        backward)
    (leftInvHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType leftInv))
        leftInv)
    (rightInvHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType rightInv))
        rightInv) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.equivIntroHet forward backward leftInv rightInv)))
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  dsimp only [Term.weaken, Term.rename, Term.subst]
  let renamedLeftInv :=
    Term.rename (TermRenaming.weakenStep context newType) leftInv
  let renamedRightInv :=
    Term.rename (TermRenaming.weakenStep context newType) rightInv
  let renamedLeftInvTypeEq :=
    equivIntroHetLeftInverseType_rename RawRenaming.weaken carrierA
      forwardRaw backwardRaw
  let renamedRightInvTypeEq :=
    equivIntroHetRightInverseType_rename RawRenaming.weaken carrierB
      forwardRaw backwardRaw
  let substitutedLeftInvWithCast :=
    Term.subst (TermSubst.singleton singletonTerm)
      (renamedLeftInvTypeEq ▸ renamedLeftInv)
  let substitutedRightInvWithCast :=
    Term.subst (TermSubst.singleton singletonTerm)
      (renamedRightInvTypeEq ▸ renamedRightInv)
  let substitutedLeftInvTypeEq :=
    equivIntroHetLeftInverseType_subst
      (Subst.singleton newType singletonRaw)
      (carrierA.rename RawRenaming.weaken)
      (forwardRaw.rename RawRenaming.weaken)
      (backwardRaw.rename RawRenaming.weaken)
  let substitutedRightInvTypeEq :=
    equivIntroHetRightInverseType_subst
      (Subst.singleton newType singletonRaw)
      (carrierB.rename RawRenaming.weaken)
      (forwardRaw.rename RawRenaming.weaken)
      (backwardRaw.rename RawRenaming.weaken)
  have leftInvInnerCastHEq :
      HEq substitutedLeftInvWithCast
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedLeftInv) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      renamedLeftInvTypeEq
      renamedLeftInv
  have rightInvInnerCastHEq :
      HEq substitutedRightInvWithCast
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedRightInv) := by
    exact Term.subst_type_eq_cast_heq
      (TermSubst.singleton singletonTerm)
      renamedRightInvTypeEq
      renamedRightInv
  have leftInvOuterCastHEq :
      HEq (substitutedLeftInvTypeEq ▸ substitutedLeftInvWithCast)
        substitutedLeftInvWithCast :=
    Term.type_eq_cast_heq substitutedLeftInvTypeEq
      substitutedLeftInvWithCast
  have rightInvOuterCastHEq :
      HEq (substitutedRightInvTypeEq ▸ substitutedRightInvWithCast)
        substitutedRightInvWithCast :=
    Term.type_eq_cast_heq substitutedRightInvTypeEq
      substitutedRightInvWithCast
  have leftInvWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedLeftInv)
        leftInv := by
    simpa only [Term.weaken] using leftInvHEq
  have rightInvWithoutCastsHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          renamedRightInv)
        rightInv := by
    simpa only [Term.weaken] using rightInvHEq
  have leftInvFullHEq :
      HEq (substitutedLeftInvTypeEq ▸ substitutedLeftInvWithCast)
        leftInv :=
    HEq.trans leftInvOuterCastHEq
      (HEq.trans leftInvInnerCastHEq leftInvWithoutCastsHEq)
  have rightInvFullHEq :
      HEq (substitutedRightInvTypeEq ▸ substitutedRightInvWithCast)
        rightInv :=
    HEq.trans rightInvOuterCastHEq
      (HEq.trans rightInvInnerCastHEq rightInvWithoutCastsHEq)
  exact Term.equivIntroHet_HEq_congr
    (Ty.weaken_subst_singleton carrierA newType singletonRaw)
    (Ty.weaken_subst_singleton carrierB newType singletonRaw)
    (RawTerm.weaken_subst_singleton forwardRaw singletonRaw)
    (RawTerm.weaken_subst_singleton backwardRaw singletonRaw)
    (RawTerm.weaken_subst_singleton leftInvRaw singletonRaw)
    (RawTerm.weaken_subst_singleton rightInvRaw singletonRaw)
    forwardHEq backwardHEq leftInvFullHEq rightInvFullHEq

/-- Equivalence application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivApp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentValueRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentValue : Term context carrierA argumentValueRaw)
    (equivHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType equivTerm))
        equivTerm)
    (argumentHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType argumentValue))
        argumentValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.equivApp equivTerm argumentValue)))
      (Term.equivApp equivTerm argumentValue) := by
  exact Term.equivApp_HEq_congr
    (Ty.weaken_subst_singleton carrierA newType singletonRaw)
    (Ty.weaken_subst_singleton carrierB newType singletonRaw)
    (RawTerm.weaken_subst_singleton equivRaw singletonRaw)
    (RawTerm.weaken_subst_singleton argumentValueRaw singletonRaw)
    equivHEq argumentHEq

/-- Univalence equivalence application preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_equivApply_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentValueRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentValue : Term context carrierA argumentValueRaw)
    (equivHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType equivTerm))
        equivTerm)
    (argumentHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType argumentValue))
        argumentValue) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType (Term.equivApply equivTerm argumentValue)))
      (Term.equivApply equivTerm argumentValue) := by
  exact Term.equivApply_HEq_congr
    (Ty.weaken_subst_singleton carrierA newType singletonRaw)
    (Ty.weaken_subst_singleton carrierB newType singletonRaw)
    (RawTerm.weaken_subst_singleton equivRaw singletonRaw)
    (RawTerm.weaken_subst_singleton argumentValueRaw singletonRaw)
    equivHEq argumentHEq

/-- Heterogeneous univalence introduction preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_uaIntroHet_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (equivWitness :
      Term context (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivWitnessHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType equivWitness))
        equivWitness) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
            equivWitness)))
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
        equivWitness) := by
  exact Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
    (Ty.weaken_subst_singleton carrierA newType singletonRaw)
    (Ty.weaken_subst_singleton carrierB newType singletonRaw)
    (RawTerm.weaken_subst_singleton carrierARaw singletonRaw)
    (RawTerm.weaken_subst_singleton carrierBRaw singletonRaw)
    (RawTerm.weaken_subst_singleton forwardRaw singletonRaw)
    (RawTerm.weaken_subst_singleton backwardRaw singletonRaw)
    equivWitnessHEq

/-- Heterogeneous funext introduction preserves weaken-then-singleton
collapse. -/
theorem Term.weaken_subst_singleton_funextIntroHet_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1))
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.funextIntroHet (context := context) domainType codomainType
            applyARaw applyBRaw)))
      (Term.funextIntroHet (context := context) domainType codomainType
        applyARaw applyBRaw) := by
  exact Term.funextIntroHet_HEq_congr
    (Ty.weaken_subst_singleton domainType newType singletonRaw)
    (Ty.weaken_subst_singleton codomainType newType singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift applyARaw singletonRaw)
    (RawTerm.weaken_lift_subst_singleton_lift applyBRaw singletonRaw)

/-- Universe cumulativity preserves weaken-then-singleton collapse. -/
theorem Term.weaken_subst_singleton_cumulUp_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {lowerLevel higherLevel : UniverseLevel}
    {cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat}
    {levelLeLow : lowerLevel.toNat + 1 ≤ level}
    {levelLeHigh : higherLevel.toNat + 1 ≤ level}
    {codeRaw : RawTerm scope}
    (newType : Ty level scope)
    {singletonRaw : RawTerm scope}
    (singletonTerm : Term context newType singletonRaw)
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeHEq :
      HEq
        (Term.subst (TermSubst.singleton singletonTerm)
          (Term.weaken newType typeCode))
        typeCode) :
    HEq
      (Term.subst (TermSubst.singleton singletonTerm)
        (Term.weaken newType
          (Term.cumulUp lowerLevel higherLevel cumulMonotone
            levelLeLow levelLeHigh typeCode)))
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) := by
  exact Term.cumulUp_HEq_congr
    (RawTerm.weaken_subst_singleton codeRaw singletonRaw)
    typeCodeHEq

/-! ## Cast-aware HEq scaffolding for Term.subst_compose

The full `Term.subst_compose` (HEq, 29 cases) is a substantial cascade
because each `lam`/`lamPi`/`appPi`/`pair`/`snd` case has internal Ty
casts that must be aligned across the two formulations.  Following the
W7-analysis: HEq cascade hits a factorization limit at typed Term level.

We attempt the cascade incrementally.  Simple constructor families
(no internal cast on the recursive call) work cleanly; cast-bearing
families are handled with the HEq tactic helpers from
`Tools/Tactics/HEq`. -/


end LeanFX2
