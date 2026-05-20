import LeanFX2.Term.RenameInjective.Core
import LeanFX2.Term.HEqCongr.Atomic.Cubical

/-! # Term/RenameInjective/CubicalCollections

Semantic leaf of the term-renaming injectivity cascade.
-/

namespace LeanFX2

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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
    cases renameEq
  · rename_i modeIsUnivalentA leftEndpointA rightEndpointA sidesPathA capA
      modeIsUnivalentB sidesB capB
    dsimp only [Term.rename] at renameEq
    cases renameEq
  · rename_i modeIsUnivalentA leftEndpointA rightEndpointA sidesPathA capA
      modeIsUnivalentB leftEndpointB rightEndpointB sidesPathB capB
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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
    dsimp only [Term.rename] at renameEq
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

end LeanFX2
