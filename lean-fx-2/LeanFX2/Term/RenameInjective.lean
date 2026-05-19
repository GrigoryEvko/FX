import LeanFX2.Term.Rename
import LeanFX2.Term.HEqCongr.Atomic
import LeanFX2.Term.HEqCongr.Compound
import LeanFX2.Foundation.RawTermInjective
import LeanFX2.Foundation.TyRenameInjective

/-! # Term/RenameInjective

Typed-term rename injectivity, built in small audited slices.

This file is the home for strength-T2.  The first slice ships the
raw-unique closed leaves: when the source raw index is a nullary raw
constructor, both typed terms are forced to be the corresponding `Term`
constructor, so the rename equality is irrelevant.
-/

namespace LeanFX2

private theorem termRenameInjectiveCastHEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term context sourceType sourceRaw) :
    HEq (typeEq ▸ sourceTerm) sourceTerm := by
  cases typeEq
  rfl

theorem Term.rename_injective_lam_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyInjective :
      ∀ (bodyA bodyB :
          Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw),
        HEq (Term.rename (termRenaming.lift domainType) bodyA)
          (Term.rename (termRenaming.lift domainType) bodyB) →
        HEq bodyA bodyB)
    (bodyA bodyB :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw) :
    Term.rename termRenaming (Term.lam bodyA) =
      Term.rename termRenaming (Term.lam bodyB) →
      Term.lam bodyA = Term.lam bodyB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  injection renameEq with contextEq domainRenameEq codomainRenameEq
    bodyRawRenameEq bodyRawRenameEqAgain bodyRenameEq
  have bodyRenameUncastHEq :
      HEq (Term.rename (termRenaming.lift domainType) bodyA)
        (Term.rename (termRenaming.lift domainType) bodyB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho codomainType)
          (Term.rename (termRenaming.lift domainType) bodyA)))
      (HEq.trans (heq_of_eq bodyRenameEq)
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho codomainType)
          (Term.rename (termRenaming.lift domainType) bodyB)))
  have bodyHEq : HEq bodyA bodyB :=
    bodyInjective bodyA bodyB bodyRenameUncastHEq
  cases bodyHEq
  rfl

theorem Term.rename_injective_app_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionInjective :
      ∀ (functionA functionB :
          Term sourceCtx (Ty.arrow domainType codomainType) functionRaw),
        HEq (Term.rename termRenaming functionA)
          (Term.rename termRenaming functionB) →
        HEq functionA functionB)
    (argumentInjective :
      ∀ (argumentA argumentB : Term sourceCtx domainType argumentRaw),
        HEq (Term.rename termRenaming argumentA)
          (Term.rename termRenaming argumentB) →
        HEq argumentA argumentB)
    (functionA functionB :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentA argumentB : Term sourceCtx domainType argumentRaw) :
    Term.rename termRenaming (Term.app functionA argumentA) =
      Term.rename termRenaming (Term.app functionB argumentB) →
      Term.app functionA argumentA = Term.app functionB argumentB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  injection renameEq with contextEq codomainRenameEq domainRenameEq
    functionRawRenameEq argumentRawRenameEq argumentRawRenameEqAgain
    functionRenameEq argumentRenameEq
  have functionHEq : HEq functionA functionB :=
    functionInjective functionA functionB (heq_of_eq functionRenameEq)
  have argumentHEq : HEq argumentA argumentB :=
    argumentInjective argumentA argumentB (heq_of_eq argumentRenameEq)
  cases functionHEq
  cases argumentHEq
  rfl

theorem Term.rename_injective_lamPi_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyInjective :
      ∀ (bodyA bodyB :
          Term (sourceCtx.cons domainType) codomainType bodyRaw),
        HEq (Term.rename (termRenaming.lift domainType) bodyA)
          (Term.rename (termRenaming.lift domainType) bodyB) →
        HEq bodyA bodyB)
    (bodyA bodyB : Term (sourceCtx.cons domainType) codomainType bodyRaw) :
    Term.rename termRenaming (Term.lamPi bodyA) =
      Term.rename termRenaming (Term.lamPi bodyB) →
      Term.lamPi bodyA = Term.lamPi bodyB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  injection renameEq with contextEq domainRenameEq codomainRenameEq
    bodyRawRenameEq bodyRawRenameEqAgain bodyRenameEq
  have bodyHEq : HEq bodyA bodyB :=
    bodyInjective bodyA bodyB (heq_of_eq bodyRenameEq)
  cases bodyHEq
  rfl

theorem Term.rename_injective_appPi_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionInjective :
      ∀ (functionA functionB :
          Term sourceCtx (Ty.piTy domainType codomainType) functionRaw),
        HEq (Term.rename termRenaming functionA)
          (Term.rename termRenaming functionB) →
        HEq functionA functionB)
    (argumentInjective :
      ∀ (argumentA argumentB : Term sourceCtx domainType argumentRaw),
        HEq (Term.rename termRenaming argumentA)
          (Term.rename termRenaming argumentB) →
        HEq argumentA argumentB)
    (functionA functionB :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw)
    (argumentA argumentB : Term sourceCtx domainType argumentRaw) :
    Term.rename termRenaming (Term.appPi functionA argumentA) =
      Term.rename termRenaming (Term.appPi functionB argumentB) →
      Term.appPi functionA argumentA = Term.appPi functionB argumentB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  have appPiRenameHEq :
      HEq
        (Term.appPi (Term.rename termRenaming functionA)
          (Term.rename termRenaming argumentA))
        (Term.appPi (Term.rename termRenaming functionB)
          (Term.rename termRenaming argumentB)) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute codomainType domainType
            argumentRaw rho).symm
          (Term.appPi (Term.rename termRenaming functionA)
            (Term.rename termRenaming argumentA))))
      (HEq.trans (heq_of_eq renameEq)
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute codomainType domainType
            argumentRaw rho).symm
          (Term.appPi (Term.rename termRenaming functionB)
            (Term.rename termRenaming argumentB))))
  injection appPiRenameHEq with contextEq domainRenameEq
    codomainRenameEq functionRawRenameEq argumentRawRenameEq
    argumentRawRenameEqAgain functionRenameEq argumentRenameEq
  have functionHEq : HEq functionA functionB :=
    functionInjective functionA functionB (heq_of_eq functionRenameEq)
  have argumentHEq : HEq argumentA argumentB :=
    argumentInjective argumentA argumentB (heq_of_eq argumentRenameEq)
  cases functionHEq
  cases argumentHEq
  rfl

theorem Term.rename_injective_effectPerform_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {effectTag : RawTerm sourceScope}
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    (operationInjective :
      ∀ (operationA operationB :
          Term sourceCtx
            (Ty.effect operationSignature.argumentCarrier effectTag)
            operationRaw),
        HEq (Term.rename termRenaming operationA)
          (Term.rename termRenaming operationB) →
        HEq operationA operationB)
    (argumentsInjective :
      ∀ (argumentsA argumentsB :
          Term sourceCtx operationSignature.argumentCarrier argumentsRaw),
        HEq (Term.rename termRenaming argumentsA)
          (Term.rename termRenaming argumentsB) →
        HEq argumentsA argumentsB)
    (operationA operationB :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (argumentsA argumentsB :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw) :
    Term.rename termRenaming
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationA argumentsA) =
      Term.rename termRenaming
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationB argumentsB) →
      Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationA argumentsA =
        Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationB argumentsB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  injection renameEq with contextEq effectTagRenameEq effectRowEq
    operationSignatureRenameEq canPerformRenameHEq operationRawRenameEq
    argumentsRawRenameEq operationRenameHEq argumentsRenameHEq
  have operationHEq : HEq operationA operationB :=
    operationInjective operationA operationB (heq_of_eq operationRenameHEq)
  have argumentsHEq : HEq argumentsA argumentsB :=
    argumentsInjective argumentsA argumentsB (heq_of_eq argumentsRenameHEq)
  cases operationHEq
  cases argumentsHEq
  rfl

theorem Term.rename_injective_universeCode_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.rename termRenaming
        (Term.universeCode (context := sourceCtx)
          innerLevel outerLevel cumulOk levelLe) =
      Term.rename termRenaming
        (Term.universeCode (context := sourceCtx)
          innerLevel outerLevel cumulOk levelLe) →
      Term.universeCode (context := sourceCtx)
          innerLevel outerLevel cumulOk levelLe =
        Term.universeCode (context := sourceCtx)
          innerLevel outerLevel cumulOk levelLe := by
  intro _renameEq
  rfl

theorem Term.rename_injective_equivReflId_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope) :
    Term.rename termRenaming
        (Term.equivReflId (context := sourceCtx) carrier) =
      Term.rename termRenaming
        (Term.equivReflId (context := sourceCtx) carrier) →
      Term.equivReflId (context := sourceCtx) carrier =
        Term.equivReflId (context := sourceCtx) carrier := by
  intro _renameEq
  rfl

theorem Term.rename_injective_funextRefl_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw) =
      Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw) →
      Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw =
        Term.funextRefl (context := sourceCtx)
          domainType codomainType applyRaw := by
  intro _renameEq
  rfl

theorem Term.rename_injective_equivReflIdAtId_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope) :
    Term.rename termRenaming
        (Term.equivReflIdAtId (context := sourceCtx)
          innerLevel innerLevelLt carrier carrierRaw) =
      Term.rename termRenaming
        (Term.equivReflIdAtId (context := sourceCtx)
          innerLevel innerLevelLt carrier carrierRaw) →
      Term.equivReflIdAtId (context := sourceCtx)
          innerLevel innerLevelLt carrier carrierRaw =
        Term.equivReflIdAtId (context := sourceCtx)
          innerLevel innerLevelLt carrier carrierRaw := by
  intro _renameEq
  rfl

theorem Term.rename_injective_funextReflAtId_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    Term.rename termRenaming
        (Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw) =
      Term.rename termRenaming
        (Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw) →
      Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw =
        Term.funextReflAtId (context := sourceCtx)
          domainType codomainType applyRaw := by
  intro _renameEq
  rfl

theorem Term.rename_injective_funextIntroHet_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    Term.rename termRenaming
        (Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw) =
      Term.rename termRenaming
        (Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw) →
      Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw =
        Term.funextIntroHet (context := sourceCtx)
          domainType codomainType applyARaw applyBRaw := by
  intro _renameEq
  rfl

theorem Term.rename_injective_equivIntroHet_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    (forwardInjective :
      ∀ (forwardA forwardB :
          Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw),
        HEq (Term.rename termRenaming forwardA)
          (Term.rename termRenaming forwardB) →
        HEq forwardA forwardB)
    (backwardInjective :
      ∀ (backwardA backwardB :
          Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw),
        HEq (Term.rename termRenaming backwardA)
          (Term.rename termRenaming backwardB) →
        HEq backwardA backwardB)
    (leftInvInjective :
      ∀ (leftInvA leftInvB :
          Term sourceCtx
            (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
            leftInvRaw),
        HEq (Term.rename termRenaming leftInvA)
          (Term.rename termRenaming leftInvB) →
        HEq leftInvA leftInvB)
    (rightInvInjective :
      ∀ (rightInvA rightInvB :
          Term sourceCtx
            (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
            rightInvRaw),
        HEq (Term.rename termRenaming rightInvA)
          (Term.rename termRenaming rightInvB) →
        HEq rightInvA rightInvB)
    (forwardA forwardB :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw)
    (backwardA backwardB :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInvA leftInvB :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw)
    (rightInvA rightInvB :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw) :
    Term.rename termRenaming
        (Term.equivIntroHet forwardA backwardA leftInvA rightInvA) =
      Term.rename termRenaming
        (Term.equivIntroHet forwardB backwardB leftInvB rightInvB) →
      Term.equivIntroHet forwardA backwardA leftInvA rightInvA =
        Term.equivIntroHet forwardB backwardB leftInvB rightInvB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  injection renameEq with contextEq carrierARenameEq carrierBRenameEq
    forwardRawRenameEq backwardRawRenameEq leftInvRawRenameEq
    rightInvRawRenameEq rightInvRawRenameEqAgain forwardRenameEq
    backwardRenameEq leftInvRenameEq rightInvRenameEq
  have forwardHEq : HEq forwardA forwardB :=
    forwardInjective forwardA forwardB (heq_of_eq forwardRenameEq)
  have backwardHEq : HEq backwardA backwardB :=
    backwardInjective backwardA backwardB (heq_of_eq backwardRenameEq)
  have leftInvRenameUncastHEq :
      HEq (Term.rename termRenaming leftInvA)
        (Term.rename termRenaming leftInvB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (equivIntroHetLeftInverseType_rename rho carrierA forwardRaw
            backwardRaw)
          (Term.rename termRenaming leftInvA)))
      (HEq.trans (heq_of_eq leftInvRenameEq)
        (termRenameInjectiveCastHEq
          (equivIntroHetLeftInverseType_rename rho carrierA forwardRaw
            backwardRaw)
          (Term.rename termRenaming leftInvB)))
  have rightInvRenameUncastHEq :
      HEq (Term.rename termRenaming rightInvA)
        (Term.rename termRenaming rightInvB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (equivIntroHetRightInverseType_rename rho carrierB forwardRaw
            backwardRaw)
          (Term.rename termRenaming rightInvA)))
      (HEq.trans (heq_of_eq rightInvRenameEq)
        (termRenameInjectiveCastHEq
          (equivIntroHetRightInverseType_rename rho carrierB forwardRaw
            backwardRaw)
          (Term.rename termRenaming rightInvB)))
  have leftInvHEq : HEq leftInvA leftInvB :=
    leftInvInjective leftInvA leftInvB leftInvRenameUncastHEq
  have rightInvHEq : HEq rightInvA rightInvB :=
    rightInvInjective rightInvA rightInvB rightInvRenameUncastHEq
  cases forwardHEq
  cases backwardHEq
  cases leftInvHEq
  cases rightInvHEq
  rfl

theorem Term.rename_injective_uaIntroHet_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (equivWitnessInjective :
      ∀ (equivWitnessA equivWitnessB :
          Term sourceCtx (Ty.equiv carrierA carrierB)
            (RawTerm.equivIntro forwardRaw backwardRaw)),
        HEq (Term.rename termRenaming equivWitnessA)
          (Term.rename termRenaming equivWitnessB) →
        HEq equivWitnessA equivWitnessB)
    (equivWitnessA equivWitnessB :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term.rename termRenaming
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
          equivWitnessA) =
      Term.rename termRenaming
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
          equivWitnessB) →
      Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
          equivWitnessA =
        Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
          equivWitnessB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  injection renameEq with contextEq innerLevelEq carrierARenameEq
    carrierBRenameEq carrierARawRenameEq carrierBRawRenameEq
    forwardRawRenameEq backwardRawRenameEq backwardRawRenameEqAgain
    equivWitnessRenameEq
  have equivWitnessHEq : HEq equivWitnessA equivWitnessB :=
    equivWitnessInjective equivWitnessA equivWitnessB
      (heq_of_eq equivWitnessRenameEq)
  cases equivWitnessHEq
  rfl

theorem Term.rename_injective_pathLam_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyInjective :
      ∀ (bodyA bodyB :
          Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw),
        HEq (Term.rename (termRenaming.lift Ty.interval) bodyA)
          (Term.rename (termRenaming.lift Ty.interval) bodyB) →
        HEq bodyA bodyB)
    (bodyA bodyB :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw) :
    Term.rename termRenaming
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyA) =
      Term.rename termRenaming
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyB) →
      Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyA =
        Term.pathLam modeIsUnivalent carrierType leftEndpoint
          rightEndpoint bodyB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  injection renameEq with contextEq carrierRenameEq modeEq
    leftEndpointRenameEq rightEndpointRenameEq bodyRawRenameEq
    bodyRenameEq
  have bodyRenameUncastHEq :
      HEq (Term.rename (termRenaming.lift Ty.interval) bodyA)
        (Term.rename (termRenaming.lift Ty.interval) bodyB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho carrierType)
          (Term.rename (termRenaming.lift Ty.interval) bodyA)))
      (HEq.trans (heq_of_eq bodyRenameEq)
        (termRenameInjectiveCastHEq
          (Ty.weaken_rename_commute rho carrierType)
          (Term.rename (termRenaming.lift Ty.interval) bodyB)))
  have bodyHEq : HEq bodyA bodyB :=
    bodyInjective bodyA bodyB bodyRenameUncastHEq
  cases bodyHEq
  rfl

theorem Term.rename_injective_atVar
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {position : Fin sourceScope}
    (termA termB :
      Term sourceCtx (varType sourceCtx position) (RawTerm.var position)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.var position)),
        Σ' (_ : genericType = varType sourceCtx position),
          HEq genericTerm (Term.var (context := sourceCtx) position) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atUnit
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.unit RawTerm.unit) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.unit),
        Σ' (_ : genericType = Ty.unit),
          HEq genericTerm (Term.unit (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atBoolTrue
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.bool RawTerm.boolTrue) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.boolTrue),
        Σ' (_ : genericType = Ty.bool),
          HEq genericTerm (Term.boolTrue (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atBoolFalse
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.bool RawTerm.boolFalse) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.boolFalse),
        Σ' (_ : genericType = Ty.bool),
          HEq genericTerm (Term.boolFalse (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atNatZero
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.nat RawTerm.natZero) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.natZero),
        Σ' (_ : genericType = Ty.nat),
          HEq genericTerm (Term.natZero (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atNatSucc_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {predecessorRaw : RawTerm sourceScope}
    (predecessorInjective :
      ∀ (predecessorA predecessorB :
          Term sourceCtx Ty.nat predecessorRaw),
        Term.rename termRenaming predecessorA =
          Term.rename termRenaming predecessorB →
        predecessorA = predecessorB)
    (termA termB :
      Term sourceCtx Ty.nat (RawTerm.natSucc predecessorRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natSucc predecessorRaw)),
        Σ' (predecessorTerm : Term sourceCtx Ty.nat predecessorRaw),
          Σ' (_ : genericType = Ty.nat),
            HEq genericTerm (Term.natSucc predecessorTerm) by
    obtain ⟨predecessorA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨predecessorB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ predecessorRenameEq
    exact congrArg Term.natSucc
      (predecessorInjective predecessorA predecessorB predecessorRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i predecessorTerm
  exact ⟨predecessorTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atNatElim_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ (scrutineeA scrutineeB : Term sourceCtx Ty.nat scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (zeroInjective :
      ∀ (zeroA zeroB : Term sourceCtx motiveType zeroRaw),
        Term.rename termRenaming zeroA = Term.rename termRenaming zeroB →
        zeroA = zeroB)
    (succInjective :
      ∀ (succA succB :
          Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw),
        Term.rename termRenaming succA = Term.rename termRenaming succB →
        succA = succB)
    (termA termB :
      Term sourceCtx motiveType
        (RawTerm.natElim scrutineeRaw zeroRaw succRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natElim scrutineeRaw zeroRaw succRaw)),
        Σ' (scrutineeTerm : Term sourceCtx Ty.nat scrutineeRaw),
          Σ' (zeroTerm : Term sourceCtx genericType zeroRaw),
            Σ' (succTerm :
                Term sourceCtx (Ty.arrow Ty.nat genericType) succRaw),
              HEq genericTerm
                (Term.natElim scrutineeTerm zeroTerm succTerm) by
    obtain ⟨scrutineeA, zeroA, succA, termHEqA⟩ := key termA
    obtain ⟨scrutineeB, zeroB, succB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ scrutineeRenameEq zeroRenameEq
      succRenameEq
    rw [scrutineeInjective scrutineeA scrutineeB scrutineeRenameEq,
      zeroInjective zeroA zeroB zeroRenameEq,
      succInjective succA succB succRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i scrutineeTerm zeroTerm succTerm
  exact ⟨scrutineeTerm, zeroTerm, succTerm, HEq.rfl⟩

theorem Term.rename_injective_atNatRec_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ (scrutineeA scrutineeB : Term sourceCtx Ty.nat scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (zeroInjective :
      ∀ (zeroA zeroB : Term sourceCtx motiveType zeroRaw),
        Term.rename termRenaming zeroA = Term.rename termRenaming zeroB →
        zeroA = zeroB)
    (succInjective :
      ∀ (succA succB :
          Term sourceCtx
            (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw),
        Term.rename termRenaming succA = Term.rename termRenaming succB →
        succA = succB)
    (termA termB :
      Term sourceCtx motiveType
        (RawTerm.natRec scrutineeRaw zeroRaw succRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.natRec scrutineeRaw zeroRaw succRaw)),
        Σ' (scrutineeTerm : Term sourceCtx Ty.nat scrutineeRaw),
          Σ' (zeroTerm : Term sourceCtx genericType zeroRaw),
            Σ' (succTerm :
                Term sourceCtx
                  (Ty.arrow Ty.nat (Ty.arrow genericType genericType))
                  succRaw),
              HEq genericTerm
                (Term.natRec scrutineeTerm zeroTerm succTerm) by
    obtain ⟨scrutineeA, zeroA, succA, termHEqA⟩ := key termA
    obtain ⟨scrutineeB, zeroB, succB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ scrutineeRenameEq zeroRenameEq
      succRenameEq
    rw [scrutineeInjective scrutineeA scrutineeB scrutineeRenameEq,
      zeroInjective zeroA zeroB zeroRenameEq,
      succInjective succA succB succRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i scrutineeTerm zeroTerm succTerm
  exact ⟨scrutineeTerm, zeroTerm, succTerm, HEq.rfl⟩

theorem Term.rename_injective_atListNil
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    (termA termB : Term sourceCtx (Ty.listType elementType) RawTerm.listNil) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.listNil),
        Σ' (elementType : Ty level sourceScope),
          Σ' (_ : genericType = Ty.listType elementType),
            HEq genericTerm
              (Term.listNil (context := sourceCtx) (elementType := elementType)) by
    obtain ⟨elementTypeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType
  exact ⟨inferredElementType, rfl, HEq.rfl⟩

theorem Term.rename_injective_atListCons_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headInjective :
      ∀ (headA headB : Term sourceCtx elementType headRaw),
        Term.rename termRenaming headA = Term.rename termRenaming headB →
        headA = headB)
    (tailInjective :
      ∀ (tailA tailB : Term sourceCtx (Ty.listType elementType) tailRaw),
        Term.rename termRenaming tailA = Term.rename termRenaming tailB →
        tailA = tailB)
    (termA termB :
      Term sourceCtx (Ty.listType elementType)
        (RawTerm.listCons headRaw tailRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.listCons headRaw tailRaw)),
        Σ' (elementType : Ty level sourceScope),
          Σ' (headTerm : Term sourceCtx elementType headRaw),
            Σ' (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw),
              Σ' (_ : genericType = Ty.listType elementType),
                HEq genericTerm (Term.listCons headTerm tailTerm) by
    obtain ⟨elementTypeA, headA, tailA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, headB, tailB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ headRenameEq tailRenameEq
    rw [headInjective headA headB headRenameEq,
      tailInjective tailA tailB tailRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType headTerm tailTerm
  exact ⟨inferredElementType, headTerm, tailTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atPair_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    (firstInjective :
      ∀ (firstA firstB : Term sourceCtx firstType firstRaw),
        Term.rename termRenaming firstA = Term.rename termRenaming firstB →
        firstA = firstB)
    (secondInjective :
      ∀ (secondA secondB :
          Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw),
        HEq (Term.rename termRenaming secondA)
          (Term.rename termRenaming secondB) →
        HEq secondA secondB)
    (termA termB :
      Term sourceCtx (Ty.sigmaTy firstType secondType)
        (RawTerm.pair firstRaw secondRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.pair firstRaw secondRaw)),
        Σ' (inferredFirstType : Ty level sourceScope),
          Σ' (inferredSecondType : Ty level (sourceScope + 1)),
            Σ' (firstValue :
                Term sourceCtx inferredFirstType firstRaw),
              Σ' (secondValue :
                  Term sourceCtx
                    (inferredSecondType.subst0 inferredFirstType firstRaw)
                    secondRaw),
                Σ' (_ :
                    genericType =
                      Ty.sigmaTy inferredFirstType inferredSecondType),
                  HEq genericTerm (Term.pair firstValue secondValue) by
    obtain ⟨inferredFirstA, inferredSecondA, firstA, secondA, typeEqA,
      termHEqA⟩ := key termA
    obtain ⟨inferredFirstB, inferredSecondB, firstB, secondB, typeEqB,
      termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq firstTypeEq secondTypeEq
      firstRawEq secondRawEq firstRenameEq secondRenameHEq
    have secondRenameUncastHEq :
        HEq (Term.rename termRenaming secondA)
          (Term.rename termRenaming secondB) :=
      HEq.trans
        (HEq.symm
          (termRenameInjectiveCastHEq
            (Ty.subst0_rename_commute secondType firstType firstRaw rho)
            (Term.rename termRenaming secondA)))
        (HEq.trans (heq_of_eq secondRenameHEq)
          (termRenameInjectiveCastHEq
            (Ty.subst0_rename_commute secondType firstType firstRaw rho)
            (Term.rename termRenaming secondB)))
    have secondHEq : HEq secondA secondB :=
      secondInjective secondA secondB secondRenameUncastHEq
    rw [firstInjective firstA firstB firstRenameEq]
    cases secondHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredFirstType inferredSecondType firstValue secondValue
  exact ⟨inferredFirstType, inferredSecondType, firstValue, secondValue, rfl,
    HEq.rfl⟩

theorem Term.rename_injective_atFst_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {firstType : Ty level sourceScope}
    {pairRaw : RawTerm sourceScope}
    (pairInjective :
      ∀ {secondA secondB : Ty level (sourceScope + 1)}
        (pairA : Term sourceCtx (Ty.sigmaTy firstType secondA) pairRaw)
        (pairB : Term sourceCtx (Ty.sigmaTy firstType secondB) pairRaw),
        HEq (Term.rename termRenaming pairA)
          (Term.rename termRenaming pairB) →
        HEq pairA pairB)
    (termA termB : Term sourceCtx firstType (RawTerm.fst pairRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.fst pairRaw)),
        Σ' (secondType : Ty level (sourceScope + 1)),
          Σ' (pairTerm :
              Term sourceCtx (Ty.sigmaTy genericType secondType) pairRaw),
            HEq genericTerm (Term.fst pairTerm) by
    obtain ⟨secondTypeA, pairA, termHEqA⟩ := key termA
    obtain ⟨secondTypeB, pairB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq firstTypeRenameEq
      secondTypeRenameEq pairRawRenameEq pairRenameHEq
    have secondTypeEq : secondTypeA = secondTypeB :=
      Ty.rename_injective_under_injective_renaming secondTypeA
        (RawRenamingInjective.lift rhoInjective) secondTypeB secondTypeRenameEq
    have pairHEq : HEq pairA pairB :=
      pairInjective pairA pairB pairRenameHEq
    cases secondTypeEq
    cases pairHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredSecondType pairTerm
  exact ⟨inferredSecondType, pairTerm, HEq.rfl⟩

theorem Term.rename_injective_snd_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairInjective :
      ∀ (pairA pairB :
          Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw),
        HEq (Term.rename termRenaming pairA)
          (Term.rename termRenaming pairB) →
        HEq pairA pairB)
    (pairA pairB :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw) :
    Term.rename termRenaming (Term.snd pairA) =
      Term.rename termRenaming (Term.snd pairB) →
      Term.snd pairA = Term.snd pairB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  have sndRenameHEq :
      HEq
        (Term.snd (Term.rename termRenaming pairA))
        (Term.snd (Term.rename termRenaming pairB)) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute secondType firstType
            (RawTerm.fst pairRaw) rho).symm
          (Term.snd (Term.rename termRenaming pairA))))
      (HEq.trans (heq_of_eq renameEq)
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute secondType firstType
            (RawTerm.fst pairRaw) rho).symm
          (Term.snd (Term.rename termRenaming pairB))))
  injection sndRenameHEq with scopeEq contextEq firstTypeRenameEq
    secondTypeRenameEq pairRawRenameEq pairRenameHEq
  have pairHEq : HEq pairA pairB :=
    pairInjective pairA pairB (heq_of_eq pairRenameHEq)
  cases pairHEq
  rfl

theorem Term.rename_injective_atGlueIntro_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRaw partialRaw : RawTerm sourceScope}
    (baseInjective :
      ∀ (baseA baseB : Term sourceCtx baseType baseRaw),
        Term.rename termRenaming baseA = Term.rename termRenaming baseB →
        baseA = baseB)
    (partialInjective :
      ∀ (partialA partialB : Term sourceCtx baseType partialRaw),
        Term.rename termRenaming partialA = Term.rename termRenaming partialB →
        partialA = partialB)
    (termA termB :
      Term sourceCtx (Ty.glue baseType boundaryWitness)
        (RawTerm.glueIntro baseRaw partialRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.glueIntro baseRaw partialRaw)),
        Σ' (modeIsUnivalent : mode = Mode.univalent),
          Σ' (inferredBaseType : Ty level sourceScope),
            Σ' (inferredBoundary : RawTerm sourceScope),
              Σ' (baseValue :
                  Term sourceCtx inferredBaseType baseRaw),
                Σ' (partialValue :
                    Term sourceCtx inferredBaseType partialRaw),
                  Σ' (_ :
                      genericType =
                        Ty.glue inferredBaseType inferredBoundary),
                    HEq genericTerm
                      (Term.glueIntro modeIsUnivalent inferredBaseType
                        inferredBoundary baseValue partialValue) by
    obtain ⟨modeIsUnivalentA, inferredBaseA, inferredBoundaryA, baseA,
      partialA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨modeIsUnivalentB, inferredBaseB, inferredBoundaryB, baseB,
      partialB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ baseRenameEq partialRenameEq
    rw [baseInjective baseA baseB baseRenameEq,
      partialInjective partialA partialB partialRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredBaseType inferredBoundary
    baseValue partialValue
  exact ⟨inferredModeIsUnivalent, inferredBaseType, inferredBoundary,
    baseValue, partialValue, rfl, HEq.rfl⟩

theorem Term.rename_injective_atGlueElim_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {baseType : Ty level sourceScope}
    {gluedRaw : RawTerm sourceScope}
    (gluedInjective :
      ∀ {boundaryA boundaryB : RawTerm sourceScope}
        (gluedA : Term sourceCtx (Ty.glue baseType boundaryA) gluedRaw)
        (gluedB : Term sourceCtx (Ty.glue baseType boundaryB) gluedRaw),
        HEq (Term.rename termRenaming gluedA)
          (Term.rename termRenaming gluedB) →
        HEq gluedA gluedB)
    (termA termB : Term sourceCtx baseType (RawTerm.glueElim gluedRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.glueElim gluedRaw)),
        Σ' (modeIsUnivalent : mode = Mode.univalent),
          Σ' (boundaryWitness : RawTerm sourceScope),
            Σ' (gluedValue :
                Term sourceCtx (Ty.glue genericType boundaryWitness) gluedRaw),
              HEq genericTerm
                (Term.glueElim modeIsUnivalent gluedValue) by
    obtain ⟨modeIsUnivalentA, boundaryA, gluedA, termHEqA⟩ := key termA
    obtain ⟨modeIsUnivalentB, boundaryB, gluedB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq baseTypeRenameEq
      boundaryRenameEq gluedRawRenameEq gluedRenameHEq
    have gluedHEq : HEq gluedA gluedB :=
      gluedInjective gluedA gluedB gluedRenameHEq
    have boundaryEq : boundaryA = boundaryB :=
      RawTerm.rename_injective_under_injective_renaming boundaryA
        rhoInjective boundaryB boundaryRenameEq
    cases boundaryEq
    cases gluedHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredBoundary gluedValue
  exact ⟨inferredModeIsUnivalent, inferredBoundary, gluedValue, HEq.rfl⟩

theorem Term.rename_injective_atTransp_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {targetType : Ty level sourceScope}
    {pathRaw sourceRaw : RawTerm sourceScope}
    (typePathInjective :
      ∀ {universeLevelA universeLevelB : UniverseLevel}
        {universeLevelLtA : universeLevelA.toNat + 1 ≤ level}
        {universeLevelLtB : universeLevelB.toNat + 1 ≤ level}
        {sourceTypeRawA sourceTypeRawB targetTypeRawA targetTypeRawB :
          RawTerm sourceScope}
        (typePathA :
          Term sourceCtx
            (Ty.path (Ty.universe universeLevelA universeLevelLtA)
              sourceTypeRawA targetTypeRawA)
            pathRaw)
        (typePathB :
          Term sourceCtx
            (Ty.path (Ty.universe universeLevelB universeLevelLtB)
              sourceTypeRawB targetTypeRawB)
            pathRaw),
        HEq (Term.rename termRenaming typePathA)
          (Term.rename termRenaming typePathB) →
        HEq typePathA typePathB)
    (sourceValueInjective :
      ∀ {sourceTypeA sourceTypeB : Ty level sourceScope}
        (sourceValueA : Term sourceCtx sourceTypeA sourceRaw)
        (sourceValueB : Term sourceCtx sourceTypeB sourceRaw),
        HEq (Term.rename termRenaming sourceValueA)
          (Term.rename termRenaming sourceValueB) →
        HEq sourceValueA sourceValueB)
    (termA termB :
      Term sourceCtx targetType (RawTerm.transp pathRaw sourceRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.transp pathRaw sourceRaw)),
        Σ' (modeIsUnivalent : mode = Mode.univalent),
          Σ' (universeLevel : UniverseLevel),
            Σ' (universeLevelLt : universeLevel.toNat + 1 ≤ level),
              Σ' (sourceType : Ty level sourceScope),
                Σ' (targetType : Ty level sourceScope),
                  Σ' (sourceTypeRaw : RawTerm sourceScope),
                    Σ' (targetTypeRaw : RawTerm sourceScope),
                      Σ' (typePath :
                          Term sourceCtx
                            (Ty.path
                              (Ty.universe universeLevel universeLevelLt)
                              sourceTypeRaw targetTypeRaw)
                            pathRaw),
                        Σ' (sourceValue :
                            Term sourceCtx sourceType sourceRaw),
                          Σ' (_ : genericType = targetType),
                            HEq genericTerm
                              (Term.transp modeIsUnivalent universeLevel
                                universeLevelLt sourceType targetType
                                sourceTypeRaw targetTypeRaw typePath
                                sourceValue) by
    obtain ⟨modeIsUnivalentA, universeLevelA, universeLevelLtA, sourceTypeA,
      targetTypeA, sourceTypeRawA, targetTypeRawA, typePathA,
      sourceValueA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨modeIsUnivalentB, universeLevelB, universeLevelLtB, sourceTypeB,
      targetTypeB, sourceTypeRawB, targetTypeRawB, typePathB,
      sourceValueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with modeEq universeLevelEq universeLevelLtEq
      sourceTypeRenameEq targetTypeRenameEq sourceTypeRawRenameEq
      targetTypeRawRenameEq pathRawRenameEq sourceRawRenameEq
      typePathRenameHEq sourceValueRenameHEq
    cases modeEq
    cases universeLevelEq
    cases universeLevelLtEq
    have sourceTypeEq : sourceTypeA = sourceTypeB :=
      Ty.rename_injective_under_injective_renaming sourceTypeA
        rhoInjective sourceTypeB sourceTypeRenameEq
    have sourceTypeRawEq : sourceTypeRawA = sourceTypeRawB :=
      RawTerm.rename_injective_under_injective_renaming sourceTypeRawA
        rhoInjective sourceTypeRawB sourceTypeRawRenameEq
    have targetTypeRawEq : targetTypeRawA = targetTypeRawB :=
      RawTerm.rename_injective_under_injective_renaming targetTypeRawA
        rhoInjective targetTypeRawB targetTypeRawRenameEq
    have typePathHEq : HEq typePathA typePathB :=
      typePathInjective typePathA typePathB typePathRenameHEq
    have sourceValueHEq : HEq sourceValueA sourceValueB :=
      sourceValueInjective sourceValueA sourceValueB sourceValueRenameHEq
    exact eq_of_heq
      (Term.transp_HEq_congr modeIsUnivalentB universeLevelA
        universeLevelLtB sourceTypeEq rfl sourceTypeRawEq
        targetTypeRawEq rfl rfl typePathHEq sourceValueHEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredUniverseLevel
    inferredUniverseLevelLt inferredSourceType inferredSourceTypeRaw
    inferredTargetTypeRaw typePath sourceValue
  exact ⟨inferredModeIsUnivalent, inferredUniverseLevel,
    inferredUniverseLevelLt, inferredSourceType, genericType,
    inferredSourceTypeRaw, inferredTargetTypeRaw, typePath, sourceValue, rfl,
    HEq.rfl⟩

theorem Term.rename_injective_atHcompFamily_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    (sidesInjective :
      ∀ {sidesTypeA sidesTypeB : Ty level sourceScope}
        (sidesA : Term sourceCtx sidesTypeA sidesRaw)
        (sidesB : Term sourceCtx sidesTypeB sidesRaw),
        HEq (Term.rename termRenaming sidesA)
          (Term.rename termRenaming sidesB) →
        HEq sidesA sidesB)
    (capInjective :
      ∀ {capTypeA capTypeB : Ty level sourceScope}
        (capA : Term sourceCtx capTypeA capRaw)
        (capB : Term sourceCtx capTypeB capRaw),
        HEq (Term.rename termRenaming capA)
          (Term.rename termRenaming capB) →
        HEq capA capB)
    (termA termB :
      Term sourceCtx carrierType (RawTerm.hcomp sidesRaw capRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  cases termA <;> cases termB
  · rename_i modeIsUnivalentA sidesA capA modeIsUnivalentB sidesB capB
    simp only [Term.rename] at renameEq
    injection renameEq with contextEq carrierTypeRenameEq
      sidesRawRenameEq capRawRenameEq modeEq sidesRenameHEq capRenameHEq
    cases modeEq
    have sidesRenameHEq' :
        HEq (Term.rename termRenaming sidesA)
          (Term.rename termRenaming sidesB) :=
      heq_of_eq sidesRenameHEq
    have capRenameHEq' :
        HEq (Term.rename termRenaming capA)
          (Term.rename termRenaming capB) :=
      heq_of_eq capRenameHEq
    have sidesHEq : HEq sidesA sidesB :=
      sidesInjective sidesA sidesB sidesRenameHEq'
    have capHEq : HEq capA capB :=
      capInjective capA capB capRenameHEq'
    exact eq_of_heq
      (Term.hcomp_HEq_congr modeIsUnivalentB rfl rfl rfl
        sidesHEq capHEq)
  · rename_i modeIsUnivalentA sidesA capA modeIsUnivalentB
      leftEndpointB rightEndpointB sidesPathB capB
    simp only [Term.rename] at renameEq
    cases renameEq
  · rename_i modeIsUnivalentA leftEndpointA rightEndpointA sidesPathA capA
      modeIsUnivalentB sidesB capB
    simp only [Term.rename] at renameEq
    cases renameEq
  · rename_i modeIsUnivalentA leftEndpointA rightEndpointA sidesPathA capA
      modeIsUnivalentB leftEndpointB rightEndpointB sidesPathB capB
    simp only [Term.rename] at renameEq
    injection renameEq with contextEq carrierTypeRenameEq modeEq
      leftEndpointRenameEq rightEndpointRenameEq sidesPathRawRenameEq
      capRawRenameEq sidesPathRenameHEq capRenameHEq
    cases modeEq
    have leftEndpointEq : leftEndpointA = leftEndpointB :=
      RawTerm.rename_injective_under_injective_renaming leftEndpointA
        rhoInjective leftEndpointB leftEndpointRenameEq
    have rightEndpointEq : rightEndpointA = rightEndpointB :=
      RawTerm.rename_injective_under_injective_renaming rightEndpointA
        rhoInjective rightEndpointB rightEndpointRenameEq
    have sidesPathHEq : HEq sidesPathA sidesPathB :=
      sidesInjective sidesPathA sidesPathB sidesPathRenameHEq
    have capRenameHEq' :
        HEq (Term.rename termRenaming capA)
          (Term.rename termRenaming capB) :=
      heq_of_eq capRenameHEq
    have capHEq : HEq capA capB :=
      capInjective capA capB capRenameHEq'
    exact eq_of_heq
      (Term.hcompPath_HEq_congr modeIsUnivalentB rfl leftEndpointEq
        rightEndpointEq rfl rfl sidesPathHEq capHEq)

theorem Term.rename_injective_atListElim_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ {matchedElementType : Ty level sourceScope}
        (scrutineeA scrutineeB :
          Term sourceCtx (Ty.listType matchedElementType) scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (nilInjective :
      ∀ (nilA nilB : Term sourceCtx motiveType nilRaw),
        Term.rename termRenaming nilA = Term.rename termRenaming nilB →
        nilA = nilB)
    (consInjective :
      ∀ {matchedElementType : Ty level sourceScope}
        (consA consB :
          Term sourceCtx
            (Ty.arrow matchedElementType
              (Ty.arrow (Ty.listType matchedElementType) motiveType))
            consRaw),
        Term.rename termRenaming consA = Term.rename termRenaming consB →
        consA = consB)
    (termA termB :
      Term sourceCtx motiveType
        (RawTerm.listElim scrutineeRaw nilRaw consRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.listElim scrutineeRaw nilRaw consRaw)),
        Σ' (elementType : Ty level sourceScope),
          Σ' (scrutineeTerm :
              Term sourceCtx (Ty.listType elementType) scrutineeRaw),
            Σ' (nilTerm : Term sourceCtx genericType nilRaw),
              Σ' (consTerm :
                  Term sourceCtx
                    (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) genericType))
                    consRaw),
                HEq genericTerm
                  (Term.listElim scrutineeTerm nilTerm consTerm) by
    obtain ⟨elementTypeA, scrutineeA, nilA, consA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, scrutineeB, nilB, consB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ elementTypeRenameEq _ _ _ _
      scrutineeRenameHEq nilRenameEq consRenameHEq
    have elementTypeEq : elementTypeA = elementTypeB :=
      Ty.rename_injective_under_injective_renaming elementTypeA
        rhoInjective elementTypeB elementTypeRenameEq
    cases elementTypeEq
    rw [scrutineeInjective scrutineeA scrutineeB
        (eq_of_heq scrutineeRenameHEq),
      nilInjective nilA nilB nilRenameEq,
      consInjective consA consB (eq_of_heq consRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType scrutineeTerm nilTerm consTerm
  exact ⟨inferredElementType, scrutineeTerm, nilTerm, consTerm, HEq.rfl⟩

theorem Term.rename_injective_atOptionNone
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    (termA termB : Term sourceCtx (Ty.optionType elementType)
      RawTerm.optionNone) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.optionNone),
        Σ' (elementType : Ty level sourceScope),
          Σ' (_ : genericType = Ty.optionType elementType),
            HEq genericTerm
              (Term.optionNone (context := sourceCtx)
                (elementType := elementType)) by
    obtain ⟨elementTypeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType
  exact ⟨inferredElementType, rfl, HEq.rfl⟩

theorem Term.rename_injective_atOptionSome_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueInjective :
      ∀ (valueA valueB : Term sourceCtx elementType valueRaw),
        Term.rename termRenaming valueA = Term.rename termRenaming valueB →
        valueA = valueB)
    (termA termB :
      Term sourceCtx (Ty.optionType elementType)
        (RawTerm.optionSome valueRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.optionSome valueRaw)),
        Σ' (elementType : Ty level sourceScope),
          Σ' (valueTerm : Term sourceCtx elementType valueRaw),
            Σ' (_ : genericType = Ty.optionType elementType),
              HEq genericTerm (Term.optionSome valueTerm) by
    obtain ⟨elementTypeA, valueA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, valueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ valueRenameEq
    exact congrArg Term.optionSome
      (valueInjective valueA valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType valueTerm
  exact ⟨inferredElementType, valueTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atOptionMatch_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ {matchedElementType : Ty level sourceScope}
        (scrutineeA scrutineeB :
          Term sourceCtx (Ty.optionType matchedElementType) scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (noneInjective :
      ∀ (noneA noneB : Term sourceCtx motiveType noneRaw),
        Term.rename termRenaming noneA = Term.rename termRenaming noneB →
        noneA = noneB)
    (someInjective :
      ∀ {matchedElementType : Ty level sourceScope}
        (someA someB :
          Term sourceCtx (Ty.arrow matchedElementType motiveType) someRaw),
        Term.rename termRenaming someA = Term.rename termRenaming someB →
        someA = someB)
    (termA termB :
      Term sourceCtx motiveType
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.optionMatch scrutineeRaw noneRaw someRaw)),
        Σ' (elementType : Ty level sourceScope),
          Σ' (scrutineeTerm :
              Term sourceCtx (Ty.optionType elementType) scrutineeRaw),
            Σ' (noneTerm : Term sourceCtx genericType noneRaw),
              Σ' (someTerm :
                  Term sourceCtx (Ty.arrow elementType genericType) someRaw),
                HEq genericTerm
                  (Term.optionMatch scrutineeTerm noneTerm someTerm) by
    obtain ⟨elementTypeA, scrutineeA, noneA, someA, termHEqA⟩ := key termA
    obtain ⟨elementTypeB, scrutineeB, noneB, someB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ elementTypeRenameEq _ _ _ _
      scrutineeRenameHEq noneRenameEq someRenameHEq
    have elementTypeEq : elementTypeA = elementTypeB :=
      Ty.rename_injective_under_injective_renaming elementTypeA
        rhoInjective elementTypeB elementTypeRenameEq
    cases elementTypeEq
    rw [scrutineeInjective scrutineeA scrutineeB
        (eq_of_heq scrutineeRenameHEq),
      noneInjective noneA noneB noneRenameEq,
      someInjective someA someB (eq_of_heq someRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredElementType scrutineeTerm noneTerm someTerm
  exact ⟨inferredElementType, scrutineeTerm, noneTerm, someTerm, HEq.rfl⟩

theorem Term.rename_injective_atEitherInl_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueInjective :
      ∀ (valueA valueB : Term sourceCtx leftType valueRaw),
        Term.rename termRenaming valueA = Term.rename termRenaming valueB →
        valueA = valueB)
    (termA termB :
      Term sourceCtx (Ty.eitherType leftType rightType)
        (RawTerm.eitherInl valueRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.eitherInl valueRaw)),
        Σ' (leftType : Ty level sourceScope),
          Σ' (rightType : Ty level sourceScope),
            Σ' (valueTerm : Term sourceCtx leftType valueRaw),
              Σ' (_ : genericType = Ty.eitherType leftType rightType),
                HEq genericTerm
                  (Term.eitherInl (rightType := rightType) valueTerm) by
    obtain ⟨leftTypeA, rightTypeA, valueA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftTypeB, rightTypeB, valueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ valueRenameEq
    exact congrArg (Term.eitherInl (rightType := rightType))
      (valueInjective valueA valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLeftType inferredRightType valueTerm
  exact ⟨inferredLeftType, inferredRightType, valueTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atEitherInr_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueInjective :
      ∀ (valueA valueB : Term sourceCtx rightType valueRaw),
        Term.rename termRenaming valueA = Term.rename termRenaming valueB →
        valueA = valueB)
    (termA termB :
      Term sourceCtx (Ty.eitherType leftType rightType)
        (RawTerm.eitherInr valueRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.eitherInr valueRaw)),
        Σ' (leftType : Ty level sourceScope),
          Σ' (rightType : Ty level sourceScope),
            Σ' (valueTerm : Term sourceCtx rightType valueRaw),
              Σ' (_ : genericType = Ty.eitherType leftType rightType),
                HEq genericTerm
                  (Term.eitherInr (leftType := leftType) valueTerm) by
    obtain ⟨leftTypeA, rightTypeA, valueA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftTypeB, rightTypeB, valueB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ valueRenameEq
    exact congrArg (Term.eitherInr (leftType := leftType))
      (valueInjective valueA valueB valueRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLeftType inferredRightType valueTerm
  exact ⟨inferredLeftType, inferredRightType, valueTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atEitherMatch_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ {matchedLeftType matchedRightType : Ty level sourceScope}
        (scrutineeA scrutineeB :
          Term sourceCtx
            (Ty.eitherType matchedLeftType matchedRightType) scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (leftInjective :
      ∀ {matchedLeftType : Ty level sourceScope}
        (leftA leftB :
          Term sourceCtx (Ty.arrow matchedLeftType motiveType) leftRaw),
        Term.rename termRenaming leftA = Term.rename termRenaming leftB →
        leftA = leftB)
    (rightInjective :
      ∀ {matchedRightType : Ty level sourceScope}
        (rightA rightB :
          Term sourceCtx (Ty.arrow matchedRightType motiveType) rightRaw),
        Term.rename termRenaming rightA = Term.rename termRenaming rightB →
        rightA = rightB)
    (termA termB :
      Term sourceCtx motiveType
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw)),
        Σ' (leftType : Ty level sourceScope),
          Σ' (rightType : Ty level sourceScope),
            Σ' (scrutineeTerm :
                Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw),
              Σ' (leftTerm :
                  Term sourceCtx (Ty.arrow leftType genericType) leftRaw),
                Σ' (rightTerm :
                  Term sourceCtx (Ty.arrow rightType genericType) rightRaw),
                  HEq genericTerm
                    (Term.eitherMatch (leftType := leftType)
                      (rightType := rightType) (motiveType := genericType)
                      scrutineeTerm leftTerm rightTerm) by
    obtain ⟨leftTypeA, rightTypeA, scrutineeA, leftA, rightA, termHEqA⟩ :=
      key termA
    obtain ⟨leftTypeB, rightTypeB, scrutineeB, leftB, rightB, termHEqB⟩ :=
      key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ leftTypeRenameEq rightTypeRenameEq _ _ _ _
      scrutineeRenameHEq leftRenameHEq rightRenameHEq
    have leftTypeEq : leftTypeA = leftTypeB :=
      Ty.rename_injective_under_injective_renaming leftTypeA
        rhoInjective leftTypeB leftTypeRenameEq
    have rightTypeEq : rightTypeA = rightTypeB :=
      Ty.rename_injective_under_injective_renaming rightTypeA
        rhoInjective rightTypeB rightTypeRenameEq
    cases leftTypeEq
    cases rightTypeEq
    rw [scrutineeInjective (matchedLeftType := leftTypeA)
        (matchedRightType := rightTypeA) scrutineeA scrutineeB
        (eq_of_heq scrutineeRenameHEq),
      leftInjective (matchedLeftType := leftTypeA) leftA leftB
        (eq_of_heq leftRenameHEq),
      rightInjective (matchedRightType := rightTypeA) rightA rightB
        (eq_of_heq rightRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLeftType inferredRightType scrutineeTerm leftTerm rightTerm
  exact ⟨inferredLeftType, inferredRightType, scrutineeTerm, leftTerm,
    rightTerm, HEq.rfl⟩

theorem Term.rename_injective_boolElim_ctor
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    (scrutineeInjective :
      ∀ (scrutineeA scrutineeB : Term sourceCtx Ty.bool scrutineeRaw),
        Term.rename termRenaming scrutineeA =
          Term.rename termRenaming scrutineeB →
        scrutineeA = scrutineeB)
    (thenInjective :
      ∀ (thenA thenB :
          Term sourceCtx
            (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw),
        HEq (Term.rename termRenaming thenA)
          (Term.rename termRenaming thenB) →
        HEq thenA thenB)
    (elseInjective :
      ∀ (elseA elseB :
          Term sourceCtx
            (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw),
        HEq (Term.rename termRenaming elseA)
          (Term.rename termRenaming elseB) →
        HEq elseA elseB)
    (scrutineeA scrutineeB : Term sourceCtx Ty.bool scrutineeRaw)
    (thenA thenB :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseA elseB :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Term.rename termRenaming
        (Term.boolElim scrutineeA thenA elseA) =
      Term.rename termRenaming
        (Term.boolElim scrutineeB thenB elseB) →
      Term.boolElim scrutineeA thenA elseA =
        Term.boolElim scrutineeB thenB elseB := by
  intro renameEq
  simp only [Term.rename] at renameEq
  have boolElimRenameHEq :
      HEq
        (Term.boolElim
          (Term.rename termRenaming scrutineeA)
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho ▸
            Term.rename termRenaming thenA)
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho ▸
            Term.rename termRenaming elseA))
        (Term.boolElim
          (Term.rename termRenaming scrutineeB)
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho ▸
            Term.rename termRenaming thenB)
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho ▸
            Term.rename termRenaming elseB)) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho).symm
          (Term.boolElim
            (Term.rename termRenaming scrutineeA)
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho ▸
              Term.rename termRenaming thenA)
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho ▸
              Term.rename termRenaming elseA))))
      (HEq.trans (heq_of_eq renameEq)
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho).symm
          (Term.boolElim
            (Term.rename termRenaming scrutineeB)
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho ▸
              Term.rename termRenaming thenB)
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho ▸
              Term.rename termRenaming elseB))))
  injection boolElimRenameHEq with scopeEq contextEq motiveRenameEq
    scrutineeRawRenameEq thenRawRenameEq elseRawRenameEq
    scrutineeRenameEq thenRenameHEq elseRenameHEq
  have thenRenameUncastHEq :
      HEq (Term.rename termRenaming thenA)
        (Term.rename termRenaming thenB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho)
          (Term.rename termRenaming thenA)))
      (HEq.trans (heq_of_eq thenRenameHEq)
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho)
          (Term.rename termRenaming thenB)))
  have elseRenameUncastHEq :
      HEq (Term.rename termRenaming elseA)
        (Term.rename termRenaming elseB) :=
    HEq.trans
      (HEq.symm
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho)
          (Term.rename termRenaming elseA)))
      (HEq.trans (heq_of_eq elseRenameHEq)
        (termRenameInjectiveCastHEq
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho)
          (Term.rename termRenaming elseB)))
  have thenHEq : HEq thenA thenB :=
    thenInjective thenA thenB thenRenameUncastHEq
  have elseHEq : HEq elseA elseB :=
    elseInjective elseA elseB elseRenameUncastHEq
  rw [scrutineeInjective scrutineeA scrutineeB scrutineeRenameEq]
  cases thenHEq
  cases elseHEq
  rfl

theorem Term.rename_injective_atIdJ_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseInjective :
      ∀ (baseA baseB : Term sourceCtx motiveType baseRaw),
        Term.rename termRenaming baseA = Term.rename termRenaming baseB →
        baseA = baseB)
    (witnessInjective :
      ∀ {carrierA carrierB : Ty level sourceScope}
        {leftEndpointA rightEndpointA leftEndpointB rightEndpointB :
          RawTerm sourceScope}
        (witnessA :
          Term sourceCtx (Ty.id carrierA leftEndpointA rightEndpointA)
            witnessRaw)
        (witnessB :
          Term sourceCtx (Ty.id carrierB leftEndpointB rightEndpointB)
            witnessRaw),
        HEq (Term.rename termRenaming witnessA)
          (Term.rename termRenaming witnessB) →
        HEq witnessA witnessB)
    (termA termB : Term sourceCtx motiveType (RawTerm.idJ baseRaw witnessRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.idJ baseRaw witnessRaw)),
        Σ' (carrier : Ty level sourceScope),
          Σ' (leftEndpoint : RawTerm sourceScope),
            Σ' (rightEndpoint : RawTerm sourceScope),
              Σ' (baseTerm : Term sourceCtx genericType baseRaw),
                Σ' (witness :
                    Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint)
                      witnessRaw),
                  HEq genericTerm (Term.idJ baseTerm witness) by
    obtain ⟨carrierA, leftEndpointA, rightEndpointA, baseA, witnessA,
      termHEqA⟩ := key termA
    obtain ⟨carrierB, leftEndpointB, rightEndpointB, baseB, witnessB,
      termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq carrierRenameEq
      leftEndpointRenameEq rightEndpointRenameEq motiveRenameEq
      baseRawRenameEq witnessRawRenameEq baseRenameEq witnessRenameHEq
    have witnessHEq : HEq witnessA witnessB :=
      witnessInjective witnessA witnessB witnessRenameHEq
    have carrierEq : carrierA = carrierB :=
      Ty.rename_injective_under_injective_renaming carrierA rhoInjective
        carrierB carrierRenameEq
    have leftEndpointEq : leftEndpointA = leftEndpointB :=
      RawTerm.rename_injective_under_injective_renaming leftEndpointA
        rhoInjective leftEndpointB leftEndpointRenameEq
    have rightEndpointEq : rightEndpointA = rightEndpointB :=
      RawTerm.rename_injective_under_injective_renaming rightEndpointA
        rhoInjective rightEndpointB rightEndpointRenameEq
    cases carrierEq
    cases leftEndpointEq
    cases rightEndpointEq
    cases witnessHEq
    rw [baseInjective baseA baseB baseRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier inferredLeftEndpoint inferredRightEndpoint
    baseTerm witnessTerm
  exact ⟨inferredCarrier, inferredLeftEndpoint, inferredRightEndpoint,
    baseTerm, witnessTerm, HEq.rfl⟩

theorem Term.rename_injective_atOEqJ_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseInjective :
      ∀ (baseA baseB : Term sourceCtx motiveType baseRaw),
        Term.rename termRenaming baseA = Term.rename termRenaming baseB →
        baseA = baseB)
    (witnessInjective :
      ∀ {carrierA carrierB : Ty level sourceScope}
        {leftEndpointA rightEndpointA leftEndpointB rightEndpointB :
          RawTerm sourceScope}
        (witnessA :
          Term sourceCtx (Ty.oeq carrierA leftEndpointA rightEndpointA)
            witnessRaw)
        (witnessB :
          Term sourceCtx (Ty.oeq carrierB leftEndpointB rightEndpointB)
            witnessRaw),
        HEq (Term.rename termRenaming witnessA)
          (Term.rename termRenaming witnessB) →
        HEq witnessA witnessB)
    (termA termB : Term sourceCtx motiveType (RawTerm.oeqJ baseRaw witnessRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.oeqJ baseRaw witnessRaw)),
        Σ' (carrier : Ty level sourceScope),
          Σ' (leftEndpoint : RawTerm sourceScope),
            Σ' (rightEndpoint : RawTerm sourceScope),
              Σ' (baseTerm : Term sourceCtx genericType baseRaw),
                Σ' (witness :
                    Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint)
                      witnessRaw),
                  HEq genericTerm (Term.oeqJ baseTerm witness) by
    obtain ⟨carrierA, leftEndpointA, rightEndpointA, baseA, witnessA,
      termHEqA⟩ := key termA
    obtain ⟨carrierB, leftEndpointB, rightEndpointB, baseB, witnessB,
      termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq carrierRenameEq
      leftEndpointRenameEq rightEndpointRenameEq motiveRenameEq
      baseRawRenameEq witnessRawRenameEq baseRenameEq witnessRenameHEq
    have witnessHEq : HEq witnessA witnessB :=
      witnessInjective witnessA witnessB witnessRenameHEq
    have carrierEq : carrierA = carrierB :=
      Ty.rename_injective_under_injective_renaming carrierA rhoInjective
        carrierB carrierRenameEq
    have leftEndpointEq : leftEndpointA = leftEndpointB :=
      RawTerm.rename_injective_under_injective_renaming leftEndpointA
        rhoInjective leftEndpointB leftEndpointRenameEq
    have rightEndpointEq : rightEndpointA = rightEndpointB :=
      RawTerm.rename_injective_under_injective_renaming rightEndpointA
        rhoInjective rightEndpointB rightEndpointRenameEq
    cases carrierEq
    cases leftEndpointEq
    cases rightEndpointEq
    cases witnessHEq
    rw [baseInjective baseA baseB baseRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier inferredLeftEndpoint inferredRightEndpoint
    baseTerm witnessTerm
  exact ⟨inferredCarrier, inferredLeftEndpoint, inferredRightEndpoint,
    baseTerm, witnessTerm, HEq.rfl⟩

theorem Term.rename_injective_atOEqFunext_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {leftFunctionRaw rightFunctionRaw pointwiseRaw : RawTerm sourceScope}
    (pointwiseInjective :
      ∀ {domainA domainB codomainA codomainB : Ty level sourceScope}
        {leftRawA rightRawA leftRawB rightRawB : RawTerm sourceScope}
        (pointwiseA :
          Term sourceCtx
            (oeqFunextPointwiseType domainA codomainA leftRawA rightRawA)
            pointwiseRaw)
        (pointwiseB :
          Term sourceCtx
            (oeqFunextPointwiseType domainB codomainB leftRawB rightRawB)
            pointwiseRaw),
        HEq (Term.rename termRenaming pointwiseA)
          (Term.rename termRenaming pointwiseB) →
        HEq pointwiseA pointwiseB)
    (termA termB :
      Term sourceCtx
        (Ty.oeq (Ty.arrow domainType codomainType)
          leftFunctionRaw rightFunctionRaw)
        (RawTerm.oeqFunext pointwiseRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.oeqFunext pointwiseRaw)),
        Σ' (matchedDomain : Ty level sourceScope),
          Σ' (matchedCodomain : Ty level sourceScope),
            Σ' (matchedLeftRaw : RawTerm sourceScope),
              Σ' (matchedRightRaw : RawTerm sourceScope),
                Σ' (pointwiseProof :
                    Term sourceCtx
                      (oeqFunextPointwiseType matchedDomain
                        matchedCodomain matchedLeftRaw matchedRightRaw)
                      pointwiseRaw),
                  Σ' (_ :
                      genericType =
                        Ty.oeq (Ty.arrow matchedDomain matchedCodomain)
                          matchedLeftRaw matchedRightRaw),
                    HEq genericTerm
                      (Term.oeqFunext matchedDomain matchedCodomain
                        matchedLeftRaw matchedRightRaw pointwiseProof) by
    obtain ⟨domainA, codomainA, leftRawA, rightRawA, pointwiseA,
      typeEqA, termHEqA⟩ := key termA
    obtain ⟨domainB, codomainB, leftRawB, rightRawB, pointwiseB,
      typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq domainRenameEq codomainRenameEq
      leftRawRenameEq rightRawRenameEq pointwiseRawRenameEq
      pointwiseRenameCastEq
    have pointwiseRenameUncastHEq :
        HEq (Term.rename termRenaming pointwiseA)
          (Term.rename termRenaming pointwiseB) :=
      HEq.trans
        (HEq.symm
          (termRenameInjectiveCastHEq
            (oeqFunextPointwiseType_rename rho domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            (Term.rename termRenaming pointwiseA)))
        (HEq.trans (heq_of_eq pointwiseRenameCastEq)
          (termRenameInjectiveCastHEq
            (oeqFunextPointwiseType_rename rho domainType codomainType
              leftFunctionRaw rightFunctionRaw)
            (Term.rename termRenaming pointwiseB)))
    have pointwiseHEq : HEq pointwiseA pointwiseB :=
      pointwiseInjective pointwiseA pointwiseB pointwiseRenameUncastHEq
    cases pointwiseHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i matchedDomain matchedCodomain matchedLeftRaw matchedRightRaw
    pointwiseProof
  exact ⟨matchedDomain, matchedCodomain, matchedLeftRaw, matchedRightRaw,
    pointwiseProof, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIdStrictRec_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseInjective :
      ∀ (baseA baseB : Term sourceCtx motiveType baseRaw),
        Term.rename termRenaming baseA = Term.rename termRenaming baseB →
        baseA = baseB)
    (witnessInjective :
      ∀ {carrierA carrierB : Ty level sourceScope}
        {leftEndpointA rightEndpointA leftEndpointB rightEndpointB :
          RawTerm sourceScope}
        (witnessA :
          Term sourceCtx (Ty.idStrict carrierA leftEndpointA rightEndpointA)
            witnessRaw)
        (witnessB :
          Term sourceCtx (Ty.idStrict carrierB leftEndpointB rightEndpointB)
            witnessRaw),
        HEq (Term.rename termRenaming witnessA)
          (Term.rename termRenaming witnessB) →
        HEq witnessA witnessB)
    (termA termB :
      Term sourceCtx motiveType (RawTerm.idStrictRec baseRaw witnessRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.idStrictRec baseRaw witnessRaw)),
        Σ' (modeIsStrict : mode = Mode.strict),
          Σ' (carrier : Ty level sourceScope),
            Σ' (leftEndpoint : RawTerm sourceScope),
              Σ' (rightEndpoint : RawTerm sourceScope),
                Σ' (baseTerm : Term sourceCtx genericType baseRaw),
                  Σ' (witness :
                      Term sourceCtx
                        (Ty.idStrict carrier leftEndpoint rightEndpoint)
                        witnessRaw),
                    HEq genericTerm
                      (Term.idStrictRec modeIsStrict baseTerm witness) by
    obtain ⟨modeIsStrictA, carrierA, leftEndpointA, rightEndpointA, baseA,
      witnessA, termHEqA⟩ := key termA
    obtain ⟨modeIsStrictB, carrierB, leftEndpointB, rightEndpointB, baseB,
      witnessB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq carrierRenameEq
      leftEndpointRenameEq rightEndpointRenameEq motiveRenameEq
      baseRawRenameEq witnessRawRenameEq baseRenameEq witnessRenameHEq
    have witnessHEq : HEq witnessA witnessB :=
      witnessInjective witnessA witnessB witnessRenameHEq
    have carrierEq : carrierA = carrierB :=
      Ty.rename_injective_under_injective_renaming carrierA rhoInjective
        carrierB carrierRenameEq
    have leftEndpointEq : leftEndpointA = leftEndpointB :=
      RawTerm.rename_injective_under_injective_renaming leftEndpointA
        rhoInjective leftEndpointB leftEndpointRenameEq
    have rightEndpointEq : rightEndpointA = rightEndpointB :=
      RawTerm.rename_injective_under_injective_renaming rightEndpointA
        rhoInjective rightEndpointB rightEndpointRenameEq
    cases carrierEq
    cases leftEndpointEq
    cases rightEndpointEq
    cases witnessHEq
    rw [baseInjective baseA baseB baseRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsStrict inferredCarrier inferredLeftEndpoint
    inferredRightEndpoint baseTerm witnessTerm
  exact ⟨inferredModeIsStrict, inferredCarrier, inferredLeftEndpoint,
    inferredRightEndpoint, baseTerm, witnessTerm, HEq.rfl⟩

theorem Term.rename_injective_atRefl
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (termA termB :
      Term sourceCtx (Ty.id carrier rawWitness rawWitness)
        (RawTerm.refl rawWitness)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.refl rawWitness)),
        Σ' (carrier : Ty level sourceScope),
          Σ' (_ : genericType = Ty.id carrier rawWitness rawWitness),
            HEq genericTerm (Term.refl carrier rawWitness) by
    obtain ⟨carrierA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨carrierB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier
  exact ⟨inferredCarrier, rfl, HEq.rfl⟩

theorem Term.rename_injective_atOEqRefl
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (termA termB :
      Term sourceCtx (Ty.oeq carrier rawWitness rawWitness)
        (RawTerm.oeqRefl rawWitness)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.oeqRefl rawWitness)),
        Σ' (carrier : Ty level sourceScope),
          Σ' (_ : genericType = Ty.oeq carrier rawWitness rawWitness),
            HEq genericTerm (Term.oeqRefl carrier rawWitness) by
    obtain ⟨carrierA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨carrierB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrier
  exact ⟨inferredCarrier, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIdStrictRefl
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (termA termB :
      Term sourceCtx (Ty.idStrict carrier rawWitness rawWitness)
        (RawTerm.idStrictRefl rawWitness)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.idStrictRefl rawWitness)),
        Σ' (modeIsStrict : mode = Mode.strict),
          Σ' (carrier : Ty level sourceScope),
            Σ' (_ : genericType = Ty.idStrict carrier rawWitness rawWitness),
              HEq genericTerm
                (Term.idStrictRefl (context := sourceCtx) modeIsStrict
                  carrier rawWitness) by
    obtain ⟨modeIsStrictA, carrierA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨modeIsStrictB, carrierB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsStrict inferredCarrier
  exact ⟨inferredModeIsStrict, inferredCarrier, rfl, HEq.rfl⟩

theorem Term.rename_injective_atInterval0
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.interval RawTerm.interval0) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.interval0),
        Σ' (_ : genericType = Ty.interval),
          HEq genericTerm (Term.interval0 (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atInterval1
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (termA termB : Term sourceCtx Ty.interval RawTerm.interval1) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType RawTerm.interval1),
        Σ' (_ : genericType = Ty.interval),
          HEq genericTerm (Term.interval1 (context := sourceCtx)) by
    obtain ⟨typeEqA, termHEqA⟩ := key termA
    obtain ⟨typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  exact ⟨rfl, HEq.rfl⟩

theorem Term.rename_injective_atIntervalOpp_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerRaw : RawTerm sourceScope}
    (innerInjective :
      ∀ (innerA innerB : Term sourceCtx Ty.interval innerRaw),
        Term.rename termRenaming innerA = Term.rename termRenaming innerB →
        innerA = innerB)
    (termA termB :
      Term sourceCtx Ty.interval (RawTerm.intervalOpp innerRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.intervalOpp innerRaw)),
        Σ' (innerTerm : Term sourceCtx Ty.interval innerRaw),
          Σ' (_ : genericType = Ty.interval),
            HEq genericTerm (Term.intervalOpp innerTerm) by
    obtain ⟨innerA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨innerB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ innerRenameEq
    exact congrArg Term.intervalOpp
      (innerInjective innerA innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTerm
  exact ⟨innerTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIntervalMeet_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftInjective :
      ∀ (leftA leftB : Term sourceCtx Ty.interval leftRaw),
        Term.rename termRenaming leftA = Term.rename termRenaming leftB →
        leftA = leftB)
    (rightInjective :
      ∀ (rightA rightB : Term sourceCtx Ty.interval rightRaw),
        Term.rename termRenaming rightA = Term.rename termRenaming rightB →
        rightA = rightB)
    (termA termB :
      Term sourceCtx Ty.interval (RawTerm.intervalMeet leftRaw rightRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.intervalMeet leftRaw rightRaw)),
        Σ' (leftTerm : Term sourceCtx Ty.interval leftRaw),
          Σ' (rightTerm : Term sourceCtx Ty.interval rightRaw),
            Σ' (_ : genericType = Ty.interval),
              HEq genericTerm (Term.intervalMeet leftTerm rightTerm) by
    obtain ⟨leftA, rightA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftB, rightB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ leftRenameEq rightRenameEq
    rw [leftInjective leftA leftB leftRenameEq,
      rightInjective rightA rightB rightRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTerm rightTerm
  exact ⟨leftTerm, rightTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIntervalJoin_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftInjective :
      ∀ (leftA leftB : Term sourceCtx Ty.interval leftRaw),
        Term.rename termRenaming leftA = Term.rename termRenaming leftB →
        leftA = leftB)
    (rightInjective :
      ∀ (rightA rightB : Term sourceCtx Ty.interval rightRaw),
        Term.rename termRenaming rightA = Term.rename termRenaming rightB →
        rightA = rightB)
    (termA termB :
      Term sourceCtx Ty.interval (RawTerm.intervalJoin leftRaw rightRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.intervalJoin leftRaw rightRaw)),
        Σ' (leftTerm : Term sourceCtx Ty.interval leftRaw),
          Σ' (rightTerm : Term sourceCtx Ty.interval rightRaw),
            Σ' (_ : genericType = Ty.interval),
              HEq genericTerm (Term.intervalJoin leftTerm rightTerm) by
    obtain ⟨leftA, rightA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨leftB, rightB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ leftRenameEq rightRenameEq
    rw [leftInjective leftA leftB leftRenameEq,
      rightInjective rightA rightB rightRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i leftTerm rightTerm
  exact ⟨leftTerm, rightTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atPathApp_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {carrierType : Ty level sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    (pathInjective :
      ∀ {leftA leftB rightA rightB : RawTerm sourceScope}
        (pathA :
          Term sourceCtx (Ty.path carrierType leftA rightA) pathRaw)
        (pathB :
          Term sourceCtx (Ty.path carrierType leftB rightB) pathRaw),
        HEq (Term.rename termRenaming pathA)
          (Term.rename termRenaming pathB) →
        HEq pathA pathB)
    (intervalInjective :
      ∀ (intervalA intervalB : Term sourceCtx Ty.interval intervalRaw),
        Term.rename termRenaming intervalA =
          Term.rename termRenaming intervalB →
        intervalA = intervalB)
    (termA termB :
      Term sourceCtx carrierType (RawTerm.pathApp pathRaw intervalRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.pathApp pathRaw intervalRaw)),
        Σ' (modeIsUnivalent : mode = Mode.univalent),
          Σ' (leftEndpoint : RawTerm sourceScope),
            Σ' (rightEndpoint : RawTerm sourceScope),
              Σ' (pathTerm :
                  Term sourceCtx
                    (Ty.path genericType leftEndpoint rightEndpoint)
                    pathRaw),
                Σ' (intervalTerm : Term sourceCtx Ty.interval intervalRaw),
                  HEq genericTerm
                    (Term.pathApp modeIsUnivalent pathTerm intervalTerm) by
    obtain ⟨modeIsUnivalentA, leftA, rightA, pathA, intervalA,
      termHEqA⟩ := key termA
    obtain ⟨modeIsUnivalentB, leftB, rightB, pathB, intervalB,
      termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq carrierTypeRenameEq
      leftRenameEq rightRenameEq pathRawRenameEq intervalRawRenameEq
      pathRenameHEq intervalRenameEq
    have leftEq : leftA = leftB :=
      RawTerm.rename_injective_under_injective_renaming leftA
        rhoInjective leftB leftRenameEq
    have rightEq : rightA = rightB :=
      RawTerm.rename_injective_under_injective_renaming rightA
        rhoInjective rightB rightRenameEq
    have pathHEq : HEq pathA pathB :=
      pathInjective pathA pathB pathRenameHEq
    have intervalEq : intervalA = intervalB :=
      intervalInjective intervalA intervalB intervalRenameEq
    cases leftEq
    cases rightEq
    cases pathHEq
    cases intervalEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredLeftEndpoint
    inferredRightEndpoint pathTerm intervalTerm
  exact ⟨inferredModeIsUnivalent, inferredLeftEndpoint,
    inferredRightEndpoint, pathTerm, intervalTerm, HEq.rfl⟩

theorem Term.rename_injective_atModIntro_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerInjective :
      ∀ (innerA innerB : Term sourceCtx innerType innerRaw),
        Term.rename termRenaming innerA = Term.rename termRenaming innerB →
        innerA = innerB)
    (termA termB :
      Term sourceCtx innerType (RawTerm.modIntro innerRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.modIntro innerRaw)),
        Σ' (innerTerm : Term sourceCtx genericType innerRaw),
          HEq genericTerm (Term.modIntro innerTerm) by
    obtain ⟨innerA, termHEqA⟩ := key termA
    obtain ⟨innerB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ innerRenameEq
    exact congrArg Term.modIntro
      (innerInjective innerA innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTerm
  exact ⟨innerTerm, HEq.rfl⟩

theorem Term.rename_injective_atModElim_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerInjective :
      ∀ (innerA innerB : Term sourceCtx innerType innerRaw),
        Term.rename termRenaming innerA = Term.rename termRenaming innerB →
        innerA = innerB)
    (termA termB :
      Term sourceCtx innerType (RawTerm.modElim innerRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.modElim innerRaw)),
        Σ' (innerTerm : Term sourceCtx genericType innerRaw),
          HEq genericTerm (Term.modElim innerTerm) by
    obtain ⟨innerA, termHEqA⟩ := key termA
    obtain ⟨innerB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ innerRenameEq
    exact congrArg Term.modElim
      (innerInjective innerA innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTerm
  exact ⟨innerTerm, HEq.rfl⟩

theorem Term.rename_injective_atSubsume_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerInjective :
      ∀ (innerA innerB : Term sourceCtx innerType innerRaw),
        Term.rename termRenaming innerA = Term.rename termRenaming innerB →
        innerA = innerB)
    (termA termB :
      Term sourceCtx innerType (RawTerm.subsume innerRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType (RawTerm.subsume innerRaw)),
        Σ' (innerTerm : Term sourceCtx genericType innerRaw),
          HEq genericTerm (Term.subsume innerTerm) by
    obtain ⟨innerA, termHEqA⟩ := key termA
    obtain ⟨innerB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ innerRenameEq
    exact congrArg Term.subsume
      (innerInjective innerA innerB innerRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i innerTerm
  exact ⟨innerTerm, HEq.rfl⟩

theorem Term.rename_injective_atRecordIntro_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (fieldInjective :
      ∀ (fieldA fieldB : Term sourceCtx singleFieldType firstRaw),
        Term.rename termRenaming fieldA = Term.rename termRenaming fieldB →
        fieldA = fieldB)
    (termA termB :
      Term sourceCtx (Ty.record singleFieldType)
        (RawTerm.recordIntro firstRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.recordIntro firstRaw)),
        Σ' (singleFieldType : Ty level sourceScope),
          Σ' (fieldTerm : Term sourceCtx singleFieldType firstRaw),
            Σ' (_ : genericType = Ty.record singleFieldType),
              HEq genericTerm (Term.recordIntro fieldTerm) by
    obtain ⟨singleFieldTypeA, fieldA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨singleFieldTypeB, fieldB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ fieldRenameEq
    exact congrArg Term.recordIntro
      (fieldInjective fieldA fieldB fieldRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredFieldType fieldTerm
  exact ⟨inferredFieldType, fieldTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atRecordProj_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordInjective :
      ∀ (recordA recordB :
          Term sourceCtx (Ty.record singleFieldType) recordRaw),
        Term.rename termRenaming recordA = Term.rename termRenaming recordB →
        recordA = recordB)
    (termA termB :
      Term sourceCtx singleFieldType (RawTerm.recordProj recordRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.recordProj recordRaw)),
        Σ' (recordTerm : Term sourceCtx (Ty.record genericType) recordRaw),
          HEq genericTerm (Term.recordProj recordTerm) by
    obtain ⟨recordA, termHEqA⟩ := key termA
    obtain ⟨recordB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ recordRenameEq
    exact congrArg Term.recordProj
      (recordInjective recordA recordB recordRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i recordTerm
  exact ⟨recordTerm, HEq.rfl⟩

theorem Term.rename_injective_atRefineIntro_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    (valueInjective :
      ∀ (valueA valueB : Term sourceCtx baseType valueRaw),
        Term.rename termRenaming valueA = Term.rename termRenaming valueB →
        valueA = valueB)
    (proofInjective :
      ∀ (proofA proofB : Term sourceCtx Ty.unit proofRaw),
        Term.rename termRenaming proofA = Term.rename termRenaming proofB →
        proofA = proofB)
    (termA termB :
      Term sourceCtx (Ty.refine baseType predicate)
        (RawTerm.refineIntro valueRaw proofRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.refineIntro valueRaw proofRaw)),
        Σ' (baseType : Ty level sourceScope),
          Σ' (predicate : RawTerm (sourceScope + 1)),
            Σ' (baseValue : Term sourceCtx baseType valueRaw),
              Σ' (predicateProof : Term sourceCtx Ty.unit proofRaw),
                Σ' (_ : genericType = Ty.refine baseType predicate),
                  HEq genericTerm
                    (Term.refineIntro predicate baseValue predicateProof) by
    obtain ⟨baseTypeA, predicateA, valueA, proofA, typeEqA,
      termHEqA⟩ := key termA
    obtain ⟨baseTypeB, predicateB, valueB, proofB, typeEqB,
      termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ valueRenameEq proofRenameEq
    rw [valueInjective valueA valueB valueRenameEq,
      proofInjective proofA proofB proofRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredBaseType inferredPredicate baseValue predicateProof
  exact ⟨inferredBaseType, inferredPredicate, baseValue, predicateProof,
    rfl, HEq.rfl⟩

theorem Term.rename_injective_atRefineElim_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {baseType : Ty level sourceScope}
    {refinedRaw : RawTerm sourceScope}
    (refinedInjective :
      ∀ {matchedPredicate : RawTerm (sourceScope + 1)}
        (refinedA refinedB :
          Term sourceCtx (Ty.refine baseType matchedPredicate) refinedRaw),
        Term.rename termRenaming refinedA = Term.rename termRenaming refinedB →
        refinedA = refinedB)
    (termA termB :
      Term sourceCtx baseType (RawTerm.refineElim refinedRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.refineElim refinedRaw)),
        Σ' (predicate : RawTerm (sourceScope + 1)),
          Σ' (refinedTerm :
              Term sourceCtx (Ty.refine genericType predicate) refinedRaw),
            HEq genericTerm (Term.refineElim refinedTerm) by
    obtain ⟨predicateA, refinedA, termHEqA⟩ := key termA
    obtain ⟨predicateB, refinedB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ predicateRenameEq _ refinedRenameHEq
    have predicateEq : predicateA = predicateB :=
      RawTerm.rename_injective_under_injective_renaming predicateA
        (RawRenamingInjective.lift rhoInjective) predicateB predicateRenameEq
    cases predicateEq
    exact congrArg Term.refineElim
      (refinedInjective refinedA refinedB (eq_of_heq refinedRenameHEq))
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredPredicate refinedTerm
  exact ⟨inferredPredicate, refinedTerm, HEq.rfl⟩

theorem Term.rename_injective_atCodataUnfold_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    (stateInjective :
      ∀ (stateA stateB : Term sourceCtx stateType stateRaw),
        Term.rename termRenaming stateA = Term.rename termRenaming stateB →
        stateA = stateB)
    (transitionInjective :
      ∀ (transitionA transitionB :
          Term sourceCtx (Ty.arrow stateType outputType) transitionRaw),
        Term.rename termRenaming transitionA =
          Term.rename termRenaming transitionB →
        transitionA = transitionB)
    (termA termB :
      Term sourceCtx (Ty.codata stateType outputType)
        (RawTerm.codataUnfold stateRaw transitionRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.codataUnfold stateRaw transitionRaw)),
        Σ' (stateType : Ty level sourceScope),
          Σ' (outputType : Ty level sourceScope),
            Σ' (stateTerm : Term sourceCtx stateType stateRaw),
              Σ' (transitionTerm :
                  Term sourceCtx (Ty.arrow stateType outputType) transitionRaw),
                Σ' (_ : genericType = Ty.codata stateType outputType),
                  HEq genericTerm
                    (Term.codataUnfold stateTerm transitionTerm) by
    obtain ⟨stateTypeA, outputTypeA, stateA, transitionA, typeEqA,
      termHEqA⟩ := key termA
    obtain ⟨stateTypeB, outputTypeB, stateB, transitionB, typeEqB,
      termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ _ _ stateRenameEq transitionRenameEq
    rw [stateInjective stateA stateB stateRenameEq,
      transitionInjective transitionA transitionB transitionRenameEq]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredStateType inferredOutputType stateTerm transitionTerm
  exact ⟨inferredStateType, inferredOutputType, stateTerm, transitionTerm,
    rfl, HEq.rfl⟩

theorem Term.rename_injective_atCodataDest_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    (codataInjective :
      ∀ {matchedStateType : Ty level sourceScope}
        (codataA codataB :
          Term sourceCtx (Ty.codata matchedStateType outputType) codataRaw),
        Term.rename termRenaming codataA = Term.rename termRenaming codataB →
        codataA = codataB)
    (termA termB :
      Term sourceCtx outputType (RawTerm.codataDest codataRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.codataDest codataRaw)),
        Σ' (stateType : Ty level sourceScope),
          Σ' (codataTerm :
              Term sourceCtx (Ty.codata stateType genericType) codataRaw),
            HEq genericTerm (Term.codataDest codataTerm) by
    obtain ⟨stateTypeA, codataA, termHEqA⟩ := key termA
    obtain ⟨stateTypeB, codataB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ stateTypeRenameEq _ _ codataRenameHEq
    have stateTypeEq : stateTypeA = stateTypeB :=
      Ty.rename_injective_under_injective_renaming stateTypeA
        rhoInjective stateTypeB stateTypeRenameEq
    cases stateTypeEq
    exact congrArg Term.codataDest
      (codataInjective codataA codataB (eq_of_heq codataRenameHEq))
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredStateType codataTerm
  exact ⟨inferredStateType, codataTerm, HEq.rfl⟩

theorem Term.rename_injective_atSessionRecv_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {protocolStep channelRaw : RawTerm sourceScope}
    (channelInjective :
      ∀ (channelA channelB :
          Term sourceCtx (Ty.session protocolStep) channelRaw),
        Term.rename termRenaming channelA = Term.rename termRenaming channelB →
        channelA = channelB)
    (termA termB :
      Term sourceCtx (Ty.session protocolStep)
        (RawTerm.sessionRecv channelRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.sessionRecv channelRaw)),
        Σ' (protocolStep : RawTerm sourceScope),
          Σ' (channelTerm :
              Term sourceCtx (Ty.session protocolStep) channelRaw),
            Σ' (_ : genericType = Ty.session protocolStep),
              HEq genericTerm (Term.sessionRecv channelTerm) by
    obtain ⟨protocolStepA, channelA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨protocolStepB, channelB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ _ channelRenameEq
    exact congrArg Term.sessionRecv
      (channelInjective channelA channelB channelRenameEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredProtocolStep channelTerm
  exact ⟨inferredProtocolStep, channelTerm, rfl, HEq.rfl⟩

theorem Term.rename_injective_atSessionSend_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {protocolStep channelRaw payloadRaw : RawTerm sourceScope}
    (channelInjective :
      ∀ (channelA channelB :
          Term sourceCtx (Ty.session protocolStep) channelRaw),
        Term.rename termRenaming channelA = Term.rename termRenaming channelB →
        channelA = channelB)
    (payloadInjective :
      ∀ {matchedPayloadType : Ty level sourceScope}
        (payloadA payloadB : Term sourceCtx matchedPayloadType payloadRaw),
        Term.rename termRenaming payloadA = Term.rename termRenaming payloadB →
        payloadA = payloadB)
    (termA termB :
      Term sourceCtx (Ty.session protocolStep)
        (RawTerm.sessionSend channelRaw payloadRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.sessionSend channelRaw payloadRaw)),
        Σ' (matchedProtocolStep : RawTerm sourceScope),
          Σ' (payloadType : Ty level sourceScope),
            Σ' (channelTerm :
                Term sourceCtx (Ty.session matchedProtocolStep) channelRaw),
              Σ' (payloadTerm : Term sourceCtx payloadType payloadRaw),
                Σ' (_ : genericType = Ty.session matchedProtocolStep),
                  HEq genericTerm
                    (Term.sessionSend matchedProtocolStep channelTerm
                      payloadTerm) by
    obtain ⟨protocolStepA, payloadTypeA, channelA, payloadA, typeEqA,
      termHEqA⟩ := key termA
    obtain ⟨protocolStepB, payloadTypeB, channelB, payloadB, typeEqB,
      termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with _ _ _ payloadTypeRenameEq _ _
      channelRenameEq payloadRenameHEq
    have payloadTypeEq : payloadTypeA = payloadTypeB :=
      Ty.rename_injective_under_injective_renaming payloadTypeA
        rhoInjective payloadTypeB payloadTypeRenameEq
    cases payloadTypeEq
    rw [channelInjective channelA channelB channelRenameEq,
      payloadInjective payloadA payloadB (eq_of_heq payloadRenameHEq)]
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredProtocolStep inferredPayloadType channelTerm payloadTerm
  exact ⟨inferredProtocolStep, inferredPayloadType, channelTerm, payloadTerm,
    rfl, HEq.rfl⟩

theorem Term.rename_injective_atArrowCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {domainCodeRaw codomainCodeRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.arrowCode (context := sourceCtx) outerLevel levelLe
                  domainCodeRaw codomainCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atPiTyCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {domainCodeRaw : RawTerm sourceScope}
    {codomainCodeRaw : RawTerm (sourceScope + 1)}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.piTyCode (context := sourceCtx) outerLevel levelLe
                  domainCodeRaw codomainCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atSigmaTyCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {domainCodeRaw : RawTerm sourceScope}
    {codomainCodeRaw : RawTerm (sourceScope + 1)}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
                  domainCodeRaw codomainCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atProductCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {firstCodeRaw secondCodeRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.productCode firstCodeRaw secondCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.productCode firstCodeRaw secondCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.productCode (context := sourceCtx) outerLevel levelLe
                  firstCodeRaw secondCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atSumCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {leftCodeRaw rightCodeRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.sumCode leftCodeRaw rightCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.sumCode leftCodeRaw rightCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.sumCode (context := sourceCtx) outerLevel levelLe
                  leftCodeRaw rightCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atListCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {elementCodeRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.listCode elementCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.listCode elementCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.listCode (context := sourceCtx) outerLevel levelLe
                  elementCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atOptionCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {elementCodeRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.optionCode elementCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.optionCode elementCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.optionCode (context := sourceCtx) outerLevel levelLe
                  elementCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atEitherCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {leftCodeRaw rightCodeRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.eitherCode leftCodeRaw rightCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.eitherCode leftCodeRaw rightCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.eitherCode (context := sourceCtx) outerLevel levelLe
                  leftCodeRaw rightCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atIdCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {typeCodeRaw leftRaw rightRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.idCode typeCodeRaw leftRaw rightRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.idCode typeCodeRaw leftRaw rightRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.idCode (context := sourceCtx) outerLevel levelLe
                  typeCodeRaw leftRaw rightRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atEquivCode
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {outerLevel : UniverseLevel}
    {levelLe : outerLevel.toNat + 1 ≤ level}
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope}
    (termA termB : Term sourceCtx (Ty.universe outerLevel levelLe)
      (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro _renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw)),
        Σ' (outerLevel : UniverseLevel),
          Σ' (levelLe : outerLevel.toNat + 1 ≤ level),
            Σ' (_ : genericType = Ty.universe outerLevel levelLe),
              HEq genericTerm
                (Term.equivCode (context := sourceCtx) outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw) by
    obtain ⟨outerLevelA, levelLeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨outerLevelB, levelLeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredOuterLevel inferredLevelLe
  exact ⟨inferredOuterLevel, inferredLevelLe, rfl, HEq.rfl⟩

theorem Term.rename_injective_atCumulUp_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {higherLevel : UniverseLevel}
    {levelLeHigh : higherLevel.toNat + 1 ≤ level}
    {codeRaw : RawTerm sourceScope}
    (codeInjective :
      ∀ {lowerLevelA lowerLevelB : UniverseLevel}
        {levelLeLowA : lowerLevelA.toNat + 1 ≤ level}
        {levelLeLowB : lowerLevelB.toNat + 1 ≤ level}
        (codeA :
          Term sourceCtx (Ty.universe lowerLevelA levelLeLowA) codeRaw)
        (codeB :
          Term sourceCtx (Ty.universe lowerLevelB levelLeLowB) codeRaw),
        HEq (Term.rename termRenaming codeA)
          (Term.rename termRenaming codeB) →
        HEq codeA codeB)
    (termA termB :
      Term sourceCtx (Ty.universe higherLevel levelLeHigh)
        (RawTerm.cumulUpMarker codeRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.cumulUpMarker codeRaw)),
        Σ' (lowerLevel : UniverseLevel),
          Σ' (higherLevel : UniverseLevel),
            Σ' (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat),
              Σ' (levelLeLow : lowerLevel.toNat + 1 ≤ level),
                Σ' (levelLeHigh : higherLevel.toNat + 1 ≤ level),
                  Σ' (typeCode :
                      Term sourceCtx
                        (Ty.universe lowerLevel levelLeLow)
                        codeRaw),
                    Σ' (_ :
                        genericType = Ty.universe higherLevel levelLeHigh),
                      HEq genericTerm
                        (Term.cumulUp (context := sourceCtx)
                          lowerLevel higherLevel cumulMonotone levelLeLow
                          levelLeHigh typeCode) by
    obtain ⟨lowerLevelA, higherLevelA, cumulMonotoneA, levelLeLowA,
      levelLeHighA, codeA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨lowerLevelB, higherLevelB, cumulMonotoneB, levelLeLowB,
      levelLeHighB, codeB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with lowerLevelEq higherLevelEq cumulMonotoneEq
      levelLeLowEq levelLeHighEq codeRenameHEq
    cases lowerLevelEq
    cases higherLevelEq
    cases cumulMonotoneEq
    cases levelLeLowEq
    cases levelLeHighEq
    have codeHEq : HEq codeA codeB :=
      codeInjective codeA codeB codeRenameHEq
    exact eq_of_heq (Term.cumulUp_HEq_congr rfl codeHEq)
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredLowerLevel inferredHigherLevel inferredCumulMonotone
    inferredLevelLeLow inferredLevelLeHigh typeCode
  exact ⟨inferredLowerLevel, inferredHigherLevel, inferredCumulMonotone,
    inferredLevelLeLow, inferredLevelLeHigh, typeCode, rfl, HEq.rfl⟩

theorem Term.rename_injective_atUaToEquiv_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {leftTy rightTy : Ty level sourceScope}
    {proofRaw : RawTerm sourceScope}
    (proofInjective :
      ∀ {innerLevelA innerLevelB : UniverseLevel}
        {innerLevelLtA : innerLevelA.toNat + 1 ≤ level}
        {innerLevelLtB : innerLevelB.toNat + 1 ≤ level}
        {leftRawA leftRawB rightRawA rightRawB : RawTerm sourceScope}
        (proofA :
          Term sourceCtx
            (Ty.id (Ty.universe innerLevelA innerLevelLtA)
              leftRawA rightRawA)
            proofRaw)
        (proofB :
          Term sourceCtx
            (Ty.id (Ty.universe innerLevelB innerLevelLtB)
              leftRawB rightRawB)
            proofRaw),
        HEq (Term.rename termRenaming proofA)
          (Term.rename termRenaming proofB) →
        HEq proofA proofB)
    (termA termB :
      Term sourceCtx (Ty.equiv leftTy rightTy)
        (RawTerm.uaToEquiv proofRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.uaToEquiv proofRaw)),
        Σ' (innerLevel : UniverseLevel),
          Σ' (innerLevelLt : innerLevel.toNat + 1 ≤ level),
            Σ' (inferredLeftTy : Ty level sourceScope),
              Σ' (inferredRightTy : Ty level sourceScope),
                Σ' (leftTyRaw : RawTerm sourceScope),
                  Σ' (rightTyRaw : RawTerm sourceScope),
                    Σ' (proof :
                        Term sourceCtx
                          (Ty.id (Ty.universe innerLevel innerLevelLt)
                            leftTyRaw rightTyRaw)
                          proofRaw),
                      Σ' (_ :
                          genericType =
                            Ty.equiv inferredLeftTy inferredRightTy),
                        HEq genericTerm
                          (Term.uaToEquiv innerLevel innerLevelLt
                            inferredLeftTy inferredRightTy
                            leftTyRaw rightTyRaw proof) by
    obtain ⟨innerLevelA, innerLevelLtA, inferredLeftA, inferredRightA,
      leftRawA, rightRawA, proofA, typeEqA, termHEqA⟩ := key termA
    obtain ⟨innerLevelB, innerLevelLtB, inferredLeftB, inferredRightB,
      leftRawB, rightRawB, proofB, typeEqB, termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq innerLevelEq innerLevelLtEq
      leftTyRenameEq rightTyRenameEq leftRawRenameEq rightRawRenameEq
      proofRenameHEq
    have proofHEq : HEq proofA proofB :=
      proofInjective proofA proofB proofRenameHEq
    have leftRawEq : leftRawA = leftRawB :=
      RawTerm.rename_injective_under_injective_renaming leftRawA
        rhoInjective leftRawB rightTyRenameEq
    have rightRawEq : rightRawA = rightRawB :=
      RawTerm.rename_injective_under_injective_renaming rightRawA
        rhoInjective rightRawB leftRawRenameEq
    cases innerLevelEq
    cases innerLevelLtEq
    cases leftRawEq
    cases rightRawEq
    cases proofHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredInnerLevel inferredInnerLevelLt inferredLeftTy
    inferredRightTy inferredLeftRaw inferredRightRaw proofTerm
  exact ⟨inferredInnerLevel, inferredInnerLevelLt, inferredLeftTy,
    inferredRightTy, inferredLeftRaw, inferredRightRaw, proofTerm, rfl,
    HEq.rfl⟩

theorem Term.rename_injective_atEquivApply_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivInjective :
      ∀ {carrierA1 carrierA2 : Ty level sourceScope}
        (equivA : Term sourceCtx (Ty.equiv carrierA1 carrierB) equivRaw)
        (equivB : Term sourceCtx (Ty.equiv carrierA2 carrierB) equivRaw),
        HEq (Term.rename termRenaming equivA)
          (Term.rename termRenaming equivB) →
        HEq equivA equivB)
    (argumentInjective :
      ∀ {carrierA1 carrierA2 : Ty level sourceScope}
        (argumentA : Term sourceCtx carrierA1 argumentRaw)
        (argumentB : Term sourceCtx carrierA2 argumentRaw),
        HEq (Term.rename termRenaming argumentA)
          (Term.rename termRenaming argumentB) →
        HEq argumentA argumentB)
    (termA termB :
      Term sourceCtx carrierB
        (RawTerm.equivApply equivRaw argumentRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.equivApply equivRaw argumentRaw)),
        Σ' (carrierA : Ty level sourceScope),
          Σ' (equivTerm :
              Term sourceCtx (Ty.equiv carrierA genericType) equivRaw),
            Σ' (argumentTerm : Term sourceCtx carrierA argumentRaw),
              HEq genericTerm
                (Term.equivApply equivTerm argumentTerm) by
    obtain ⟨carrierA1, equivA, argumentA, termHEqA⟩ := key termA
    obtain ⟨carrierA2, equivB, argumentB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq carrierARenameEq
      carrierBRenameEq equivRawRenameEq argumentRawRenameEq equivRenameHEq
      argumentRenameHEq
    have equivHEq : HEq equivA equivB :=
      equivInjective equivA equivB equivRenameHEq
    have argumentHEq : HEq argumentA argumentB :=
      argumentInjective argumentA argumentB argumentRenameHEq
    have carrierAEq : carrierA1 = carrierA2 :=
      Ty.rename_injective_under_injective_renaming carrierA1
        rhoInjective carrierA2 carrierARenameEq
    cases carrierAEq
    cases equivHEq
    cases argumentHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrierA equivTerm argumentTerm
  exact ⟨inferredCarrierA, equivTerm, argumentTerm, HEq.rfl⟩

theorem Term.rename_injective_atEquivApp_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivInjective :
      ∀ {carrierA1 carrierA2 : Ty level sourceScope}
        (equivA : Term sourceCtx (Ty.equiv carrierA1 carrierB) equivRaw)
        (equivB : Term sourceCtx (Ty.equiv carrierA2 carrierB) equivRaw),
        HEq (Term.rename termRenaming equivA)
          (Term.rename termRenaming equivB) →
        HEq equivA equivB)
    (argumentInjective :
      ∀ {carrierA1 carrierA2 : Ty level sourceScope}
        (argumentA : Term sourceCtx carrierA1 argumentRaw)
        (argumentB : Term sourceCtx carrierA2 argumentRaw),
        HEq (Term.rename termRenaming argumentA)
          (Term.rename termRenaming argumentB) →
        HEq argumentA argumentB)
    (termA termB :
      Term sourceCtx carrierB
        (RawTerm.equivApp equivRaw argumentRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.equivApp equivRaw argumentRaw)),
        Σ' (carrierA : Ty level sourceScope),
          Σ' (equivTerm :
              Term sourceCtx (Ty.equiv carrierA genericType) equivRaw),
            Σ' (argumentTerm : Term sourceCtx carrierA argumentRaw),
              HEq genericTerm
                (Term.equivApp equivTerm argumentTerm) by
    obtain ⟨carrierA1, equivA, argumentA, termHEqA⟩ := key termA
    obtain ⟨carrierA2, equivB, argumentB, termHEqB⟩ := key termB
    cases termHEqA
    cases termHEqB
    simp only [Term.rename] at renameEq
    injection renameEq with scopeEq contextEq carrierARenameEq
      carrierBRenameEq equivRawRenameEq argumentRawRenameEq equivRenameHEq
      argumentRenameHEq
    have equivHEq : HEq equivA equivB :=
      equivInjective equivA equivB equivRenameHEq
    have argumentHEq : HEq argumentA argumentB :=
      argumentInjective argumentA argumentB argumentRenameHEq
    have carrierAEq : carrierA1 = carrierA2 :=
      Ty.rename_injective_under_injective_renaming carrierA1
        rhoInjective carrierA2 carrierARenameEq
    cases carrierAEq
    cases equivHEq
    cases argumentHEq
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredCarrierA equivTerm argumentTerm
  exact ⟨inferredCarrierA, equivTerm, argumentTerm, HEq.rfl⟩

/-- Inversion for the shared `RawTerm.equivIntro` raw head.

The raw head is intentionally shared by the canonical identity equivalence,
its universe-Id witness, heterogeneous equivalence introduction, and
heterogeneous univalence introduction.  Keeping the target type free avoids
the dependent-elimination wall at call sites that only know the raw shape. -/
def Term.equivIntro_inv
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {targetType : Ty level scope}
    {forwardRaw backwardRaw : RawTerm scope}
    (genericTerm :
      Term context targetType (RawTerm.equivIntro forwardRaw backwardRaw)) :
    (Σ' (carrier : Ty level scope)
        (_ :
          forwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ :
          backwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ : targetType = Ty.equiv carrier carrier),
        HEq genericTerm (Term.equivReflId (context := context) carrier)) ⊕'
    (Σ' (innerLevel : UniverseLevel)
        (innerLevelLt : innerLevel.toNat + 1 ≤ level)
        (carrier : Ty level scope)
        (carrierRaw : RawTerm scope)
        (_ :
          forwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ :
          backwardRaw =
            RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (_ :
          targetType =
            Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw
              carrierRaw),
        HEq genericTerm
          (Term.equivReflIdAtId (context := context) innerLevel innerLevelLt
            carrier carrierRaw)) ⊕'
    (Σ' (carrierLeft carrierRight : Ty level scope)
        (leftInvRaw rightInvRaw : RawTerm scope)
        (forward :
          Term context (Ty.arrow carrierLeft carrierRight) forwardRaw)
        (backward :
          Term context (Ty.arrow carrierRight carrierLeft) backwardRaw)
        (leftInv :
          Term context
            (equivIntroHetLeftInverseType carrierLeft forwardRaw backwardRaw)
            leftInvRaw)
        (rightInv :
          Term context
            (equivIntroHetRightInverseType carrierRight forwardRaw backwardRaw)
            rightInvRaw)
        (_ : targetType = Ty.equiv carrierLeft carrierRight),
        HEq genericTerm
          (Term.equivIntroHet forward backward leftInv rightInv)) ⊕'
    (Σ' (innerLevel : UniverseLevel)
        (innerLevelLt : innerLevel.toNat + 1 ≤ level)
        (carrierLeft carrierRight : Ty level scope)
        (carrierLeftRaw carrierRightRaw : RawTerm scope)
        (equivWitness :
          Term context (Ty.equiv carrierLeft carrierRight)
            (RawTerm.equivIntro forwardRaw backwardRaw))
        (_ :
          targetType =
            Ty.id (Ty.universe innerLevel innerLevelLt) carrierLeftRaw
              carrierRightRaw),
        HEq genericTerm
          (Term.uaIntroHet innerLevel innerLevelLt carrierLeftRaw
            carrierRightRaw equivWitness)) := by
  cases genericTerm
  case equivReflId carrier =>
    exact PSum.inl ⟨carrier, rfl, rfl, rfl, HEq.rfl⟩
  case equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
    exact PSum.inr (PSum.inl
      ⟨innerLevel, innerLevelLt, carrier, carrierRaw, rfl, rfl, rfl,
        HEq.rfl⟩)
  case equivIntroHet forward backward leftInv rightInv =>
    exact PSum.inr (PSum.inr (PSum.inl
      ⟨_, _, _, _, forward, backward, leftInv, rightInv, rfl, HEq.rfl⟩))
  case uaIntroHet innerLevel innerLevelLt carrierLeft carrierRight
      carrierLeftRaw carrierRightRaw equivWitness =>
    exact PSum.inr (PSum.inr (PSum.inr
      ⟨innerLevel, innerLevelLt, carrierLeft, carrierRight, carrierLeftRaw,
        carrierRightRaw, equivWitness, rfl, HEq.rfl⟩))

theorem Term.rename_injective_atEquivIntroEquiv_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (childInjective :
      ∀ {childTypeA childTypeB : Ty level sourceScope}
        {childRawA childRawB : RawTerm sourceScope}
        (childA : Term sourceCtx childTypeA childRawA)
        (childB : Term sourceCtx childTypeB childRawB),
        HEq (Term.rename termRenaming childA)
          (Term.rename termRenaming childB) →
        HEq childA childB)
    (termA termB :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  have viewA := Term.equivIntro_inv termA
  have viewB := Term.equivIntro_inv termB
  cases viewA with
  | inl reflViewA =>
    obtain ⟨carrierLeft, forwardEqA, backwardEqA, typeEqA, termHEqA⟩ :=
      reflViewA
    cases typeEqA
    cases forwardEqA
    cases backwardEqA
    cases termHEqA
    cases viewB with
    | inl reflViewB =>
      obtain ⟨carrierRight, forwardEqB, backwardEqB, typeEqB, termHEqB⟩ :=
        reflViewB
      cases typeEqB
      cases forwardEqB
      cases backwardEqB
      cases termHEqB
      exact rfl
    | inr restViewB =>
      cases restViewB with
      | inl idViewB =>
        obtain ⟨innerLevelB, innerLevelLtB, carrierRight, carrierRawB,
          forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
        cases typeEqB
      | inr restViewB =>
        cases restViewB with
        | inl introViewB =>
          obtain ⟨carrierLeftB, carrierRightB, leftInvRawB, rightInvRawB,
            forwardB, backwardB, leftInvB, rightInvB, typeEqB,
            termHEqB⟩ := introViewB
          cases typeEqB
          cases termHEqB
          simp only [Term.rename] at renameEq
          cases renameEq
        | inr uaViewB =>
          obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB, carrierRightB,
            carrierLeftRawB, carrierRightRawB, equivWitnessB, typeEqB,
            termHEqB⟩ := uaViewB
          cases typeEqB
  | inr restViewA =>
    cases restViewA with
    | inl idViewA =>
      obtain ⟨innerLevelA, innerLevelLtA, carrierLeft, carrierRawA,
        forwardEqA, backwardEqA, typeEqA, termHEqA⟩ := idViewA
      cases typeEqA
    | inr restViewA =>
      cases restViewA with
      | inl introViewA =>
        obtain ⟨carrierLeftA, carrierRightA, leftInvRawA, rightInvRawA,
          forwardA, backwardA, leftInvA, rightInvA, typeEqA,
          termHEqA⟩ := introViewA
        cases typeEqA
        cases termHEqA
        cases viewB with
        | inl reflViewB =>
          obtain ⟨carrierRight, forwardEqB, backwardEqB, typeEqB,
            termHEqB⟩ := reflViewB
          cases typeEqB
          cases forwardEqB
          cases backwardEqB
          cases termHEqB
          simp only [Term.rename] at renameEq
          cases renameEq
        | inr restViewB =>
          cases restViewB with
          | inl idViewB =>
            obtain ⟨innerLevelB, innerLevelLtB, carrierRight, carrierRawB,
              forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
            cases typeEqB
          | inr restViewB =>
            cases restViewB with
            | inl introViewB =>
              obtain ⟨carrierLeftB, carrierRightB, leftInvRawB,
                rightInvRawB, forwardB, backwardB, leftInvB, rightInvB,
                typeEqB, termHEqB⟩ := introViewB
              cases typeEqB
              cases termHEqB
              simp only [Term.rename] at renameEq
              injection renameEq with contextEq carrierLeftRenameEq
                carrierRightRenameEq forwardRawRenameEq backwardRawRenameEq
                backwardRawRenameEqAgain leftInvRawRenameEq rightInvRawRenameEq
                forwardRenameEq backwardRenameEq leftInvRenameEq
                rightInvRenameEq
              have leftInvRawEq : leftInvRawA = leftInvRawB :=
                RawTerm.rename_injective_under_injective_renaming leftInvRawA
                  rhoInjective leftInvRawB leftInvRawRenameEq
              have rightInvRawEq : rightInvRawA = rightInvRawB :=
                RawTerm.rename_injective_under_injective_renaming
                  rightInvRawA rhoInjective rightInvRawB rightInvRawRenameEq
              have forwardHEq : HEq forwardA forwardB :=
                childInjective forwardA forwardB (heq_of_eq forwardRenameEq)
              have backwardHEq : HEq backwardA backwardB :=
                childInjective backwardA backwardB (heq_of_eq backwardRenameEq)
              have leftInvRenameUncastHEq :
                  HEq (Term.rename termRenaming leftInvA)
                    (Term.rename termRenaming leftInvB) :=
                HEq.trans
                  (HEq.symm
                    (termRenameInjectiveCastHEq
                      (equivIntroHetLeftInverseType_rename rho carrierA
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming leftInvA)))
                  (HEq.trans leftInvRenameEq
                    (termRenameInjectiveCastHEq
                      (equivIntroHetLeftInverseType_rename rho carrierA
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming leftInvB)))
              have rightInvRenameUncastHEq :
                  HEq (Term.rename termRenaming rightInvA)
                    (Term.rename termRenaming rightInvB) :=
                HEq.trans
                  (HEq.symm
                    (termRenameInjectiveCastHEq
                      (equivIntroHetRightInverseType_rename rho carrierB
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming rightInvA)))
                  (HEq.trans rightInvRenameEq
                    (termRenameInjectiveCastHEq
                      (equivIntroHetRightInverseType_rename rho carrierB
                        forwardRaw backwardRaw)
                      (Term.rename termRenaming rightInvB)))
              have leftInvHEq : HEq leftInvA leftInvB :=
                childInjective leftInvA leftInvB leftInvRenameUncastHEq
              have rightInvHEq : HEq rightInvA rightInvB :=
                childInjective rightInvA rightInvB rightInvRenameUncastHEq
              exact eq_of_heq
                (Term.equivIntroHet_HEq_congr rfl rfl rfl rfl
                  leftInvRawEq rightInvRawEq forwardHEq
                  backwardHEq leftInvHEq rightInvHEq)
            | inr uaViewB =>
              obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB,
                carrierRightB, carrierLeftRawB, carrierRightRawB,
                equivWitnessB, typeEqB, termHEqB⟩ := uaViewB
              cases typeEqB
      | inr uaViewA =>
        obtain ⟨innerLevelA, innerLevelLtA, carrierLeftA, carrierRightA,
          carrierLeftRawA, carrierRightRawA, equivWitnessA, typeEqA,
          termHEqA⟩ := uaViewA
        cases typeEqA

theorem Term.rename_injective_atEquivIntroUniverseId_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {innerLevel : UniverseLevel}
    {innerLevelLt : innerLevel.toNat + 1 ≤ level}
    {leftRaw rightRaw : RawTerm sourceScope}
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (childInjective :
      ∀ {childTypeA childTypeB : Ty level sourceScope}
        {childRawA childRawB : RawTerm sourceScope}
        (childA : Term sourceCtx childTypeA childRawA)
        (childB : Term sourceCtx childTypeB childRawB),
        HEq (Term.rename termRenaming childA)
          (Term.rename termRenaming childB) →
        HEq childA childB)
    (termA termB :
      Term sourceCtx (Ty.id (Ty.universe innerLevel innerLevelLt)
        leftRaw rightRaw)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  have viewA := Term.equivIntro_inv termA
  have viewB := Term.equivIntro_inv termB
  cases viewA with
  | inl reflViewA =>
    obtain ⟨carrierA, forwardEqA, backwardEqA, typeEqA, termHEqA⟩ :=
      reflViewA
    cases typeEqA
  | inr restViewA =>
    cases restViewA with
    | inl idViewA =>
      obtain ⟨innerLevelA, innerLevelLtA, carrierA, carrierRawA,
        forwardEqA, backwardEqA, typeEqA, termHEqA⟩ := idViewA
      cases typeEqA
      cases forwardEqA
      cases backwardEqA
      cases termHEqA
      cases viewB with
      | inl reflViewB =>
        obtain ⟨carrierB, forwardEqB, backwardEqB, typeEqB, termHEqB⟩ :=
          reflViewB
        cases typeEqB
      | inr restViewB =>
        cases restViewB with
        | inl idViewB =>
          obtain ⟨innerLevelB, innerLevelLtB, carrierB, carrierRawB,
            forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
          cases typeEqB
          cases forwardEqB
          cases backwardEqB
          cases termHEqB
          simp only [Term.rename] at renameEq
          injection renameEq with contextEq innerLevelEq innerLevelLtEq
            carrierRenameEq carrierRawRenameEq
          cases innerLevelEq
          cases innerLevelLtEq
          have carrierEq : carrierA = carrierB :=
            Ty.rename_injective_under_injective_renaming carrierA rhoInjective
              carrierB carrierRenameEq
          exact eq_of_heq
            (Term.equivReflIdAtId_HEq_congr carrierEq rfl)
        | inr restViewB =>
          cases restViewB with
          | inl introViewB =>
            obtain ⟨carrierLeftB, carrierRightB, leftInvRawB, rightInvRawB,
              forwardB, backwardB, leftInvB, rightInvB, typeEqB,
              termHEqB⟩ := introViewB
            cases typeEqB
          | inr uaViewB =>
            obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB, carrierRightB,
              carrierLeftRawB, carrierRightRawB, equivWitnessB, typeEqB,
              termHEqB⟩ := uaViewB
            cases typeEqB
            cases termHEqB
            simp only [Term.rename] at renameEq
            cases renameEq
    | inr restViewA =>
      cases restViewA with
      | inl introViewA =>
        obtain ⟨carrierLeftA, carrierRightA, leftInvRawA, rightInvRawA,
          forwardA, backwardA, leftInvA, rightInvA, typeEqA,
          termHEqA⟩ := introViewA
        cases typeEqA
      | inr uaViewA =>
        obtain ⟨innerLevelA, innerLevelLtA, carrierLeftA, carrierRightA,
          carrierLeftRawA, carrierRightRawA, equivWitnessA, typeEqA,
          termHEqA⟩ := uaViewA
        cases typeEqA
        cases termHEqA
        cases viewB with
        | inl reflViewB =>
          obtain ⟨carrierB, forwardEqB, backwardEqB, typeEqB, termHEqB⟩ :=
            reflViewB
          cases typeEqB
        | inr restViewB =>
          cases restViewB with
          | inl idViewB =>
            obtain ⟨innerLevelB, innerLevelLtB, carrierB, carrierRawB,
              forwardEqB, backwardEqB, typeEqB, termHEqB⟩ := idViewB
            cases typeEqB
            cases forwardEqB
            cases backwardEqB
            cases termHEqB
            simp only [Term.rename] at renameEq
            cases renameEq
          | inr restViewB =>
            cases restViewB with
            | inl introViewB =>
              obtain ⟨carrierLeftB, carrierRightB, leftInvRawB,
                rightInvRawB, forwardB, backwardB, leftInvB, rightInvB,
                typeEqB, termHEqB⟩ := introViewB
              cases typeEqB
            | inr uaViewB =>
              obtain ⟨innerLevelB, innerLevelLtB, carrierLeftB,
                carrierRightB, carrierLeftRawB, carrierRightRawB,
                equivWitnessB, typeEqB, termHEqB⟩ := uaViewB
              cases typeEqB
              cases termHEqB
              simp only [Term.rename] at renameEq
              injection renameEq with contextEq innerLevelEq innerLevelLtEq
                carrierLeftRenameEq carrierRightRenameEq carrierLeftRawRenameEq
                carrierRightRawRenameEq forwardRawRenameEq backwardRawRenameEq
                equivWitnessRenameEq
              cases innerLevelEq
              cases innerLevelLtEq
              have carrierLeftEq : carrierLeftA = carrierLeftB :=
                Ty.rename_injective_under_injective_renaming carrierLeftA
                  rhoInjective carrierLeftB carrierLeftRenameEq
              have carrierRightEq : carrierRightA = carrierRightB :=
                Ty.rename_injective_under_injective_renaming carrierRightA
                  rhoInjective carrierRightB carrierRightRenameEq
              have carrierLeftRawEq : leftRaw = leftRaw := rfl
              have carrierRightRawEq : rightRaw = rightRaw := rfl
              have equivWitnessHEq : HEq equivWitnessA equivWitnessB :=
                childInjective equivWitnessA equivWitnessB
                  equivWitnessRenameEq
              exact eq_of_heq
                (Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
                  carrierLeftEq carrierRightEq carrierLeftRawEq
                  carrierRightRawEq rfl rfl equivWitnessHEq)

theorem Term.rename_injective_atEquivIntro_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (rhoInjective : RawRenamingInjective rho)
    {targetType : Ty level sourceScope}
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (childInjective :
      ∀ {childTypeA childTypeB : Ty level sourceScope}
        {childRawA childRawB : RawTerm sourceScope}
        (childA : Term sourceCtx childTypeA childRawA)
        (childB : Term sourceCtx childTypeB childRawB),
        HEq (Term.rename termRenaming childA)
          (Term.rename termRenaming childB) →
        HEq childA childB)
    (termA termB :
      Term sourceCtx targetType
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  have viewA := Term.equivIntro_inv termA
  cases viewA with
  | inl reflViewA =>
    obtain ⟨carrier, forwardEq, backwardEq, typeEq, termHEq⟩ := reflViewA
    cases typeEq
    exact
      Term.rename_injective_atEquivIntroEquiv_of_inner termRenaming
        rhoInjective childInjective termA termB renameEq
  | inr restViewA =>
    cases restViewA with
    | inl idViewA =>
      obtain ⟨innerLevel, innerLevelLt, carrier, carrierRaw, forwardEq,
        backwardEq, typeEq, termHEq⟩ := idViewA
      cases typeEq
      exact
        Term.rename_injective_atEquivIntroUniverseId_of_inner termRenaming
          rhoInjective childInjective termA termB renameEq
    | inr restViewA =>
      cases restViewA with
      | inl introViewA =>
        obtain ⟨carrierLeft, carrierRight, leftInvRaw, rightInvRaw,
          forwardTerm, backwardTerm, leftInv, rightInv, typeEq, termHEq⟩ :=
          introViewA
        cases typeEq
        exact
          Term.rename_injective_atEquivIntroEquiv_of_inner termRenaming
            rhoInjective childInjective termA termB renameEq
      | inr uaViewA =>
        obtain ⟨innerLevel, innerLevelLt, carrierLeft, carrierRight,
          carrierLeftRaw, carrierRightRaw, equivWitness, typeEq,
          termHEq⟩ := uaViewA
        cases typeEq
        exact
          Term.rename_injective_atEquivIntroUniverseId_of_inner termRenaming
            rhoInjective childInjective termA termB renameEq

end LeanFX2
