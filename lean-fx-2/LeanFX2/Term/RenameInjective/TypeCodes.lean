import LeanFX2.Term.RenameInjective.Core
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT

/-! # Term/RenameInjective/TypeCodes

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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

end LeanFX2
