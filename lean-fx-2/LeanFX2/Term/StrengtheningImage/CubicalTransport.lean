import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/CubicalTransport

Soundness lemmas for cubical glue elimination, path application success, and transport producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for cubical Glue-elimination strengthening.  Mirrors the
RefineElim/CodataDest OfSuccess pattern: the wrapper's dual
`Option.casesOn` on `Ty.glue`'s base + boundary pivots is replaced by
pre-witnessed `baseSuccess`/`boundarySuccess` in the OfSuccess. -/
theorem partialStrengthenTypedGlueElimOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {targetBaseType : Ty level targetScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {targetBoundaryWitness targetGluedRaw : RawTerm targetScope}
    {gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    {targetGluedValue :
      Term targetCtx (Ty.glue targetBaseType targetBoundaryWitness)
        targetGluedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundarySuccess :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    (gluedRawStrengthens :
      gluedRaw.partialStrengthen? strengthening.back = some targetGluedRaw)
    (gluedRawRenames :
      gluedRaw = targetGluedRaw.rename strengthening.forward)
    (gluedSound :
      HEq gluedValue
        (Term.rename strengthening.toTermRenaming targetGluedValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedGlueElimOfSuccess modeIsUnivalent
        (gluedValue := gluedValue) targetGluedValue baseSuccess
        boundarySuccess gluedRawStrengthens gluedRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedGlueElimOfSuccess]
  have baseRenames :
      baseType = targetBaseType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  have boundaryRenames :
      boundaryWitness =
        targetBoundaryWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename boundaryWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBoundaryWitness boundarySuccess
  exact Term.glueElim_HEq_congr modeIsUnivalent baseRenames boundaryRenames
    gluedRawRenames gluedSound

/-- Soundness for the typed glue-elimination wrapper.

Mirrors `partialStrengthenTypedGlueElim`'s App-pattern shape: the
wrapper takes `baseSuccess` and `boundarySuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
base type and boundary witness respectively).  The proof destructures
the glued value's `StrengtheningResult`, aligns the `Ty.glue` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedGlueElimOfSuccess_sound`.  Same recipe as
Phase 39 RefineElim / Phase 40 CodataDest. -/
theorem partialStrengthenTypedGlueElim_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {targetBaseType : Ty level targetScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {targetBoundaryWitness : RawTerm targetScope}
    {gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundarySuccess :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    {gluedResult : StrengtheningResult strengthening gluedValue}
    (gluedSound : StrengtheningSoundness gluedResult) :
    StrengtheningSoundness
      (partialStrengthenTypedGlueElim modeIsUnivalent baseSuccess
        boundarySuccess gluedResult) := by
  cases gluedResult with
  | mk targetGluedType targetGluedRaw targetGluedValue
      gluedTypeStrengthens gluedRawStrengthens gluedTypeRenames
      gluedRawRenames =>
      have expectedGluedTypeStrengthens :
          (Ty.glue baseType boundaryWitness).partialStrengthen?
              strengthening.back =
            some (Ty.glue targetBaseType targetBoundaryWitness) := by
        change
          Option.mapTwo
            (baseType.partialStrengthen? strengthening.back)
            (boundaryWitness.partialStrengthen? strengthening.back)
            Ty.glue =
              some (Ty.glue targetBaseType targetBoundaryWitness)
        rw [baseSuccess, boundarySuccess]
        rfl
      rw [expectedGluedTypeStrengthens] at gluedTypeStrengthens
      cases gluedTypeStrengthens
      exact partialStrengthenTypedGlueElimOfSuccess_sound
        modeIsUnivalent
        (baseSuccess := baseSuccess)
        (boundarySuccess := boundarySuccess)
        (gluedRawStrengthens := gluedRawStrengthens)
        (gluedRawRenames := gluedRawRenames)
        gluedSound.termRenames

/-- Soundness for cubical path-application strengthening (OfSuccess
form).

Mirrors the GlueElim/RefineElim recipe: takes pre-witnessed
strengthening of the path's carrier + left + right endpoints + raw
forms, plus HEq witnesses for the path/interval sub-terms.  Recovers
the syntactic equalities via `partialStrengthen?_imp_rename` and
applies `pathApp_HEq_congr`.

The wrapper `partialStrengthenTypedPathApp` does a dual `Option.casesOn`
on the three Ty.path pivots; the OfSuccess pre-witnesses them, sparing
the soundness proof from re-doing that dance. -/
theorem partialStrengthenTypedPathAppOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {targetPathRaw targetIntervalRaw : RawTerm targetScope}
    {pathTerm :
      Term sourceCtx
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    {targetPathTerm :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetPathRaw}
    {targetIntervalTerm :
      Term targetCtx Ty.interval targetIntervalRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (pathRawStrengthens :
      pathRaw.partialStrengthen? strengthening.back = some targetPathRaw)
    (intervalRawStrengthens :
      intervalRaw.partialStrengthen? strengthening.back =
        some targetIntervalRaw)
    (pathRawRenames :
      pathRaw = targetPathRaw.rename strengthening.forward)
    (intervalRawRenames :
      intervalRaw = targetIntervalRaw.rename strengthening.forward)
    (pathSound :
      HEq pathTerm
        (Term.rename strengthening.toTermRenaming targetPathTerm))
    (intervalSound :
      HEq intervalTerm
        (Term.rename strengthening.toTermRenaming targetIntervalTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedPathAppOfSuccess modeIsUnivalent
        (pathTerm := pathTerm) (intervalTerm := intervalTerm)
        targetPathTerm targetIntervalTerm carrierSuccess leftSuccess
        rightSuccess pathRawStrengthens intervalRawStrengthens
        pathRawRenames intervalRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedPathAppOfSuccess]
  have carrierRenames :
      carrierType = targetCarrierType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierSuccess
  have leftEndpointRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightEndpointRenames :
      rightEndpoint =
        targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.pathApp_HEq_congr modeIsUnivalent carrierRenames
    leftEndpointRenames rightEndpointRenames pathRawRenames
    intervalRawRenames pathSound intervalSound

/-- Soundness of `partialStrengthenTypedTranspOfSuccess`: the result's
renamed target term is heterogeneously equal to the original typed
transport.  Composes with `Term.transp_HEq_congr` plus
`partialStrengthen?_imp_rename` for the type / raw equalities. -/
theorem partialStrengthenTypedTranspOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {sourceType targetType : Ty level sourceScope}
    {targetSourceType targetTargetType : Ty level targetScope}
    {sourceTypeRaw targetTypeRaw : RawTerm sourceScope}
    {targetSourceTypeRaw targetTargetTypeRaw : RawTerm targetScope}
    {pathRaw sourceRaw : RawTerm sourceScope}
    {targetPathRaw targetSourceRaw : RawTerm targetScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    {targetPath :
      Term targetCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          targetSourceTypeRaw targetTargetTypeRaw)
        targetPathRaw}
    {targetSourceValue :
      Term targetCtx targetSourceType targetSourceRaw}
    (sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (targetTypeRawStrengthens :
      targetTypeRaw.partialStrengthen? strengthening.back =
        some targetTargetTypeRaw)
    (pathRawStrengthens :
      pathRaw.partialStrengthen? strengthening.back =
        some targetPathRaw)
    (sourceRawStrengthens :
      sourceRaw.partialStrengthen? strengthening.back =
        some targetSourceRaw)
    (pathRawRenames :
      pathRaw = targetPathRaw.rename strengthening.forward)
    (sourceRawRenames :
      sourceRaw = targetSourceRaw.rename strengthening.forward)
    (pathSound :
      HEq typePath
        (Term.rename strengthening.toTermRenaming targetPath))
    (sourceSound :
      HEq sourceValue
        (Term.rename strengthening.toTermRenaming targetSourceValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedTranspOfSuccess modeIsUnivalent
        universeLevel universeLevelLt
        (typePath := typePath) (sourceValue := sourceValue)
        targetPath targetSourceValue sourceTypeStrengthens
        targetTypeStrengthens sourceTypeRawStrengthens
        targetTypeRawStrengthens pathRawStrengthens sourceRawStrengthens
        pathRawRenames sourceRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedTranspOfSuccess]
  have sourceTypeRenames :
      sourceType = targetSourceType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename sourceType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetSourceType sourceTypeStrengthens
  have targetTypeRenames :
      targetType = targetTargetType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename targetType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetTargetType targetTypeStrengthens
  have sourceTypeRawRenames :
      sourceTypeRaw =
        targetSourceTypeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename sourceTypeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetSourceTypeRaw sourceTypeRawStrengthens
  have targetTypeRawRenames :
      targetTypeRaw =
        targetTargetTypeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename targetTypeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetTargetTypeRaw targetTypeRawStrengthens
  exact Term.transp_HEq_congr modeIsUnivalent universeLevel
    universeLevelLt sourceTypeRenames targetTypeRenames
    sourceTypeRawRenames targetTypeRawRenames pathRawRenames
    sourceRawRenames pathSound sourceSound

/-- Soundness for the typed-transport strengthening wrapper.

The wrapper inline-constructs a `StrengtheningResult` after splitting the
path and source-value results.  This soundness mirror parallels those
splits, aligns the path type via the expected path-strengthening
equation, and discharges via `Term.transp_HEq_congr`. -/
theorem partialStrengthenTypedTransp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (targetSourceType targetTargetType : Ty level targetScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    (targetSourceTypeRaw targetTargetTypeRaw : RawTerm targetScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (targetTypeRawStrengthens :
      targetTypeRaw.partialStrengthen? strengthening.back =
        some targetTargetTypeRaw)
    {pathResult : StrengtheningResult strengthening typePath}
    {sourceResult : StrengtheningResult strengthening sourceValue}
    (pathSound : StrengtheningSoundness pathResult)
    (sourceSound : StrengtheningSoundness sourceResult) :
    StrengtheningSoundness
      (partialStrengthenTypedTransp modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType targetSourceType
        targetTargetType sourceTypeRaw targetTypeRaw
        targetSourceTypeRaw targetTargetTypeRaw
        sourceTypeStrengthens targetTypeStrengthens
        sourceTypeRawStrengthens targetTypeRawStrengthens
        pathResult sourceResult) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPath pathTypeStrengthens
      pathRawStrengthens pathTypeRenames pathRawRenames =>
      have expectedPathTypeStrengthens :
          (Ty.path (Ty.universe universeLevel universeLevelLt)
              sourceTypeRaw targetTypeRaw).partialStrengthen?
              strengthening.back =
            some (Ty.path (Ty.universe universeLevel universeLevelLt)
              targetSourceTypeRaw targetTargetTypeRaw) := by
        change
          Option.mapThree
            ((Ty.universe universeLevel universeLevelLt).partialStrengthen?
              strengthening.back)
            (sourceTypeRaw.partialStrengthen? strengthening.back)
            (targetTypeRaw.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path (Ty.universe universeLevel universeLevelLt)
                targetSourceTypeRaw targetTargetTypeRaw)
        rw [sourceTypeRawStrengthens, targetTypeRawStrengthens]
        rfl
      rw [expectedPathTypeStrengthens] at pathTypeStrengthens
      cases pathTypeStrengthens
      cases sourceResult with
      | mk targetSourceValueType targetSourceRaw targetSourceValue
          sourceValueTypeStrengthens sourceRawStrengthens
          sourceValueTypeRenames sourceRawRenames =>
          rw [sourceTypeStrengthens] at sourceValueTypeStrengthens
          cases sourceValueTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedTransp,
              StrengtheningResult.renamedTarget]
            at pathSound sourceSound ⊢
          have sourceTypeRenames :
              sourceType = targetSourceType.rename strengthening.forward :=
            Ty.partialStrengthen?_imp_rename sourceType
              strengthening.forward strengthening.back
              strengthening.injectsBack targetSourceType
              sourceTypeStrengthens
          have targetTypeRenames :
              targetType = targetTargetType.rename strengthening.forward :=
            Ty.partialStrengthen?_imp_rename targetType
              strengthening.forward strengthening.back
              strengthening.injectsBack targetTargetType
              targetTypeStrengthens
          have sourceTypeRawRenames :
              sourceTypeRaw =
                targetSourceTypeRaw.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename sourceTypeRaw
              strengthening.forward strengthening.back
              strengthening.injectsBack targetSourceTypeRaw
              sourceTypeRawStrengthens
          have targetTypeRawRenames :
              targetTypeRaw =
                targetTargetTypeRaw.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename targetTypeRaw
              strengthening.forward strengthening.back
              strengthening.injectsBack targetTargetTypeRaw
              targetTypeRawStrengthens
          exact Term.transp_HEq_congr modeIsUnivalent universeLevel
            universeLevelLt sourceTypeRenames targetTypeRenames
            sourceTypeRawRenames targetTypeRawRenames pathRawRenames
            sourceRawRenames pathSound.termRenames
            sourceSound.termRenames

end Term

end LeanFX2
