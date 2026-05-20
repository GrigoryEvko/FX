import LeanFX2.Term.RenameInjective.Core

/-! # Term/RenameInjective/ConstructorFamilies

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

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
  dsimp only [Term.rename] at renameEq
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
  dsimp only [Term.rename] at renameEq
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
  dsimp only [Term.rename] at renameEq
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
  dsimp only [Term.rename] at renameEq
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
  dsimp only [Term.rename] at renameEq
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

theorem Term.rename_injective_effectPerform_ctor_proofIrrel
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {effectTag : RawTerm sourceScope}
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (canPerformA canPerformB :
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
          canPerformA operationA argumentsA) =
      Term.rename termRenaming
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformB operationB argumentsB) →
      Term.effectPerform effectTag effectRow operationSignature
          canPerformA operationA argumentsA =
        Term.effectPerform effectTag effectRow operationSignature
          canPerformB operationB argumentsB := by
  intro renameEq
  dsimp only [Term.rename] at renameEq
  injection renameEq with contextEq effectTagRenameEq effectRowEq
    operationSignatureRenameEq canPerformRenameHEq operationRawRenameEq
    argumentsRawRenameEq operationRenameHEq argumentsRenameHEq
  have operationHEq : HEq operationA operationB :=
    operationInjective operationA operationB (heq_of_eq operationRenameHEq)
  have argumentsHEq : HEq argumentsA argumentsB :=
    argumentsInjective argumentsA argumentsB (heq_of_eq argumentsRenameHEq)
  cases operationHEq
  cases argumentsHEq
  have canPerformEq : canPerformA = canPerformB :=
    proof_irrel canPerformA canPerformB
  cases canPerformEq
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
  dsimp only [Term.rename] at renameEq
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
  dsimp only [Term.rename] at renameEq
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
  dsimp only [Term.rename] at renameEq
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

theorem Term.rename_injective_atPathLam_of_inner
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyInjective :
      ∀ {carrierA carrierB : Ty level sourceScope}
        (bodyA : Term (sourceCtx.cons Ty.interval) carrierA.weaken bodyRaw)
        (bodyB : Term (sourceCtx.cons Ty.interval) carrierB.weaken bodyRaw),
        HEq (Term.rename (termRenaming.lift Ty.interval) bodyA)
          (Term.rename (termRenaming.lift Ty.interval) bodyB) →
        HEq bodyA bodyB)
    (termA termB :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        (RawTerm.pathLam bodyRaw)) :
    Term.rename termRenaming termA = Term.rename termRenaming termB →
      termA = termB := by
  intro renameEq
  suffices key :
      ∀ {genericType : Ty level sourceScope}
        (genericTerm : Term sourceCtx genericType
          (RawTerm.pathLam bodyRaw)),
        Σ' (modeIsUnivalent : mode = Mode.univalent),
          Σ' (genericCarrier : Ty level sourceScope),
            Σ' (genericLeft : RawTerm sourceScope),
              Σ' (genericRight : RawTerm sourceScope),
                Σ' (bodyTerm :
                    Term (sourceCtx.cons Ty.interval)
                      genericCarrier.weaken bodyRaw),
                  Σ' (_ :
                      genericType =
                        Ty.path genericCarrier genericLeft genericRight),
                    HEq genericTerm
                      (Term.pathLam modeIsUnivalent genericCarrier
                        genericLeft genericRight bodyTerm) by
    obtain ⟨modeIsUnivalentA, carrierA, leftA, rightA, bodyA, typeEqA,
      termHEqA⟩ := key termA
    obtain ⟨modeIsUnivalentB, carrierB, leftB, rightB, bodyB, typeEqB,
      termHEqB⟩ := key termB
    cases typeEqA
    cases typeEqB
    cases termHEqA
    cases termHEqB
    dsimp only [Term.rename] at renameEq
    injection renameEq with contextEq carrierRenameEq modeEq
      leftEndpointRenameEq rightEndpointRenameEq bodyRawRenameEq
      bodyRenameEq
    cases modeEq
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
    cases modeIsUnivalentA
    cases modeIsUnivalentB
    rfl
  intro genericType genericTerm
  cases genericTerm
  rename_i inferredModeIsUnivalent inferredCarrier inferredLeftEndpoint
    inferredRightEndpoint bodyTerm
  exact ⟨inferredModeIsUnivalent, inferredCarrier, inferredLeftEndpoint,
    inferredRightEndpoint, bodyTerm, rfl, HEq.rfl⟩

end LeanFX2
