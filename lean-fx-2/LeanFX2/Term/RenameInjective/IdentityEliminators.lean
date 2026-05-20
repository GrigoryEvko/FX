import LeanFX2.Term.RenameInjective.Core

/-! # Term/RenameInjective/IdentityEliminators

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

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
  dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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

end LeanFX2
