import LeanFX2.Term.RenameInjective.ReflexivityInterval

/-! # Term/RenameInjective/ModalStructural

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

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

end LeanFX2
