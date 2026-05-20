import LeanFX2.Term.PartialStrengthen.Constructors.HeterogeneousIntro

/-! # Term/PartialStrengthen/Constructors/Cubical

Typed partial-strengthening producers for cubical glue, transport, and
homogeneous composition terms.
-/

namespace LeanFX2

namespace Term

/-- Glue introduction strengthens by strengthening both payload values
at the same strengthened base type and strengthening the schematic
boundary witness. -/
def partialStrengthenTypedGlueIntro {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (targetBaseType : Ty level targetScope)
    (boundaryWitness : RawTerm sourceScope)
    (targetBoundaryWitness : RawTerm targetScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseTypeStrengthens :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundaryStrengthens :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    (baseResult : StrengtheningResult strengthening baseValue)
    (partialResult : StrengtheningResult strengthening partialValue) :
    StrengtheningResult strengthening
      (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
        boundaryWitness baseValue partialValue) := by
  cases baseResult with
  | mk targetBaseValueType targetBaseRaw targetBaseValue
      baseValueTypeStrengthens baseRawStrengthens baseValueTypeRenames
      baseRawRenames =>
      rw [baseTypeStrengthens] at baseValueTypeStrengthens
      cases baseValueTypeStrengthens
      cases partialResult with
      | mk targetPartialValueType targetPartialRaw targetPartialValue
          partialValueTypeStrengthens partialRawStrengthens
          partialValueTypeRenames partialRawRenames =>
          rw [baseTypeStrengthens] at partialValueTypeStrengthens
          cases partialValueTypeStrengthens
          exact {
            targetType := Ty.glue targetBaseType targetBoundaryWitness
            targetRaw := RawTerm.glueIntro targetBaseRaw targetPartialRaw
            targetTerm :=
              Term.glueIntro (context := targetCtx) modeIsUnivalent
                targetBaseType targetBoundaryWitness targetBaseValue
                targetPartialValue
            typeStrengthens := by
              change
                Option.mapTwo
                  (baseType.partialStrengthen? strengthening.back)
                  (boundaryWitness.partialStrengthen? strengthening.back)
                  Ty.glue =
                    some (Ty.glue targetBaseType targetBoundaryWitness)
              rw [baseTypeStrengthens, boundaryStrengthens]
              rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (baseRaw.partialStrengthen? strengthening.back)
                  (partialRaw.partialStrengthen? strengthening.back)
                  RawTerm.glueIntro =
                    some (RawTerm.glueIntro targetBaseRaw targetPartialRaw)
              rw [baseRawStrengthens, partialRawStrengthens]
              rfl
            typeRenames := by
              exact
                Ty.partialStrengthen?_imp_rename
                  (Ty.glue baseType boundaryWitness)
                  strengthening.forward strengthening.back
                  strengthening.injectsBack
                  (Ty.glue targetBaseType targetBoundaryWitness)
                  (by
                    change
                      Option.mapTwo
                        (baseType.partialStrengthen? strengthening.back)
                        (boundaryWitness.partialStrengthen?
                          strengthening.back)
                        Ty.glue =
                          some (Ty.glue targetBaseType
                            targetBoundaryWitness)
                    rw [baseTypeStrengthens, boundaryStrengthens]
                    rfl)
            rawRenames := by
              cases baseRawRenames
              cases partialRawRenames
              rfl
          }

/-- Success branch for cubical Glue-elimination strengthening.  Takes
pre-decomposed witnesses for the glue carrier's base + boundary pivots
plus the strengthened glued-value.  Splits out the term-mode body so
soundness skips the wrapper's dual `Option.casesOn` discriminator wall
over `Ty.glue`. -/
def partialStrengthenTypedGlueElimOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {targetBaseType : Ty level targetScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {targetBoundaryWitness targetGluedRaw : RawTerm targetScope}
    {gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (targetGluedValue :
      Term targetCtx (Ty.glue targetBaseType targetBoundaryWitness)
        targetGluedRaw)
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (_boundarySuccess :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    (gluedRawStrengthens :
      gluedRaw.partialStrengthen? strengthening.back = some targetGluedRaw)
    (gluedRawRenames :
      gluedRaw = targetGluedRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.glueElim (context := sourceCtx) modeIsUnivalent gluedValue) where
  targetType := targetBaseType
  targetRaw := RawTerm.glueElim targetGluedRaw
  targetTerm := Term.glueElim (context := targetCtx) modeIsUnivalent
    targetGluedValue
  typeStrengthens := baseSuccess
  rawStrengthens := by
    change
      (match gluedRaw.partialStrengthen? strengthening.back with
      | some strengthenedGlued =>
          some (RawTerm.glueElim strengthenedGlued)
      | none => none) =
        some (RawTerm.glueElim targetGluedRaw)
    rw [gluedRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  rawRenames := by
    cases gluedRawRenames
    rfl

/-- Glue elimination strengthens by decomposing the strengthened glue
carrier of the eliminated value.

App-pattern: takes `baseSuccess` and `boundarySuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
base type and boundary witness respectively).  The body destructures
the glued value's `StrengtheningResult`, aligns the `Ty.glue` shape
via `rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedGlueElimOfSuccess`.  Identical 2-option-split
recipe to Phase 39 RefineElim / Phase 40 CodataDest. -/
def partialStrengthenTypedGlueElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
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
    (gluedResult : StrengtheningResult strengthening gluedValue) :
    StrengtheningResult strengthening
      (Term.glueElim (context := sourceCtx) modeIsUnivalent gluedValue) := by
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
      exact partialStrengthenTypedGlueElimOfSuccess
        modeIsUnivalent targetGluedValue baseSuccess
        boundarySuccess gluedRawStrengthens gluedRawRenames

/-- OfSuccess variant of `partialStrengthenTypedTransp` that consumes
pre-witnessed strengthening data for both the typed path and source
children, sparing the soundness proof from replicating the wrapper's
`cases pathResult` / `cases sourceResult` dance.  Reusable from any
caller that has already extracted the typed Path / source witnesses
via separate strengthening lookups (or constructed them directly). -/
def partialStrengthenTypedTranspOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
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
    (targetPath :
      Term targetCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          targetSourceTypeRaw targetTargetTypeRaw)
        targetPathRaw)
    (targetSourceValue :
      Term targetCtx targetSourceType targetSourceRaw)
    (_sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (_sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (_targetTypeRawStrengthens :
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
      sourceRaw = targetSourceRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) where
  targetType := targetTargetType
  targetRaw := RawTerm.transp targetPathRaw targetSourceRaw
  targetTerm :=
    Term.transp (context := targetCtx) modeIsUnivalent
      universeLevel universeLevelLt targetSourceType
      targetTargetType targetSourceTypeRaw targetTargetTypeRaw
      targetPath targetSourceValue
  typeStrengthens := targetTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (pathRaw.partialStrengthen? strengthening.back)
        (sourceRaw.partialStrengthen? strengthening.back)
        RawTerm.transp =
          some (RawTerm.transp targetPathRaw targetSourceRaw)
    rw [pathRawStrengthens, sourceRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename targetType
      strengthening.forward strengthening.back
      strengthening.injectsBack targetTargetType
      targetTypeStrengthens
  rawRenames := by
    cases pathRawRenames
    cases sourceRawRenames
    rfl

/-- Cubical transport strengthens by strengthening the path proof, the
source value, and the schematic source/target carrier data. -/
def partialStrengthenTypedTransp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
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
    (pathResult : StrengtheningResult strengthening typePath)
    (sourceResult : StrengtheningResult strengthening sourceValue) :
    StrengtheningResult strengthening
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPath
      pathTypeStrengthens pathRawStrengthens pathTypeRenames pathRawRenames =>
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
          exact {
            targetType := targetTargetType
            targetRaw := RawTerm.transp targetPathRaw targetSourceRaw
            targetTerm :=
              Term.transp (context := targetCtx) modeIsUnivalent
                universeLevel universeLevelLt targetSourceType
                targetTargetType targetSourceTypeRaw targetTargetTypeRaw
                targetPath targetSourceValue
            typeStrengthens := targetTypeStrengthens
            rawStrengthens := by
              change
                Option.mapTwo
                  (pathRaw.partialStrengthen? strengthening.back)
                  (sourceRaw.partialStrengthen? strengthening.back)
                  RawTerm.transp =
                    some (RawTerm.transp targetPathRaw targetSourceRaw)
              rw [pathRawStrengthens, sourceRawStrengthens]
              rfl
            typeRenames :=
              Ty.partialStrengthen?_imp_rename targetType
                strengthening.forward strengthening.back
                strengthening.injectsBack targetTargetType
                targetTypeStrengthens
            rawRenames := by
              cases pathRawRenames
              cases sourceRawRenames
              rfl
          }

/-- OfSuccess variant of `partialStrengthenTypedHcomp` consuming
pre-witnessed strengthening data for both typed children, sparing the
soundness proof from the wrapper's nested `cases sidesResult` /
`cases capResult` dance. -/
def partialStrengthenTypedHcompOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {targetSidesRaw targetCapRaw : RawTerm targetScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (targetSidesValue :
      Term targetCtx targetCarrierType targetSidesRaw)
    (targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw)
    (carrierStrengthens :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (sidesRawStrengthens :
      sidesRaw.partialStrengthen? strengthening.back =
        some targetSidesRaw)
    (capRawStrengthens :
      capRaw.partialStrengthen? strengthening.back =
        some targetCapRaw)
    (sidesRawRenames :
      sidesRaw = targetSidesRaw.rename strengthening.forward)
    (capRawRenames :
      capRaw = targetCapRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.hcomp (context := sourceCtx) modeIsUnivalent sidesValue
        capValue) where
  targetType := targetCarrierType
  targetRaw := RawTerm.hcomp targetSidesRaw targetCapRaw
  targetTerm :=
    Term.hcomp (context := targetCtx) modeIsUnivalent
      targetSidesValue targetCapValue
  typeStrengthens := carrierStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (sidesRaw.partialStrengthen? strengthening.back)
        (capRaw.partialStrengthen? strengthening.back)
        RawTerm.hcomp =
          some (RawTerm.hcomp targetSidesRaw targetCapRaw)
    rw [sidesRawStrengthens, capRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back
      strengthening.injectsBack targetCarrierType
      carrierStrengthens
  rawRenames := by
    cases sidesRawRenames
    cases capRawRenames
    rfl

/-- Homogeneous composition strengthens by strengthening both carrier
payloads at the same strengthened carrier type. -/
def partialStrengthenTypedHcomp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesResult : StrengtheningResult strengthening sidesValue)
    (capResult : StrengtheningResult strengthening capValue) :
    StrengtheningResult strengthening
      (Term.hcomp (context := sourceCtx) modeIsUnivalent sidesValue
        capValue) := by
  cases sidesResult with
  | mk targetCarrierType targetSidesRaw targetSidesValue
      carrierStrengthens sidesRawStrengthens carrierRenames
      sidesRawRenames =>
      cases capResult with
      | mk targetCapType targetCapRaw targetCapValue capTypeStrengthens
          capRawStrengthens capTypeRenames capRawRenames =>
          rw [carrierStrengthens] at capTypeStrengthens
          cases capTypeStrengthens
          exact {
            targetType := targetCarrierType
            targetRaw := RawTerm.hcomp targetSidesRaw targetCapRaw
            targetTerm :=
              Term.hcomp (context := targetCtx) modeIsUnivalent
                targetSidesValue targetCapValue
            typeStrengthens := carrierStrengthens
            rawStrengthens := by
              change
                Option.mapTwo
                  (sidesRaw.partialStrengthen? strengthening.back)
                  (capRaw.partialStrengthen? strengthening.back)
                  RawTerm.hcomp =
                    some (RawTerm.hcomp targetSidesRaw targetCapRaw)
              rw [sidesRawStrengthens, capRawStrengthens]
              rfl
            typeRenames := carrierRenames
            rawRenames := by
              cases sidesRawRenames
              cases capRawRenames
              rfl
          }

/-- Pre-witnessed path-shaped homogeneous composition strengthening.

Replaces the wrapper's nested `Option.casesOn` on `Ty.path`'s
carrier + leftEndpoint + rightEndpoint pivots with explicit
strengthening witnesses for each.  The unused
`_leftSuccess`/`_rightSuccess` are kept in the signature so the
OfSuccess-sound theorem can recover the endpoint renaming
equalities used by `hcompPath_HEq_congr`. -/
def partialStrengthenTypedHcompPathOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {targetSidesPathRaw targetCapRaw : RawTerm targetScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (targetSidesPath :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetSidesPathRaw)
    (targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw)
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (sidesPathRawStrengthens :
      sidesPathRaw.partialStrengthen? strengthening.back =
        some targetSidesPathRaw)
    (capRawStrengthens :
      capRaw.partialStrengthen? strengthening.back =
        some targetCapRaw)
    (sidesPathRawRenames :
      sidesPathRaw = targetSidesPathRaw.rename strengthening.forward)
    (capRawRenames :
      capRaw = targetCapRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.hcompPath (context := sourceCtx) modeIsUnivalent
        leftEndpoint rightEndpoint sidesPath capValue) where
  targetType := targetCarrierType
  targetRaw := RawTerm.hcomp targetSidesPathRaw targetCapRaw
  targetTerm :=
    Term.hcompPath (context := targetCtx) modeIsUnivalent
      targetLeftEndpoint targetRightEndpoint targetSidesPath
      targetCapValue
  typeStrengthens := carrierSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (sidesPathRaw.partialStrengthen? strengthening.back)
        (capRaw.partialStrengthen? strengthening.back)
        RawTerm.hcomp =
          some (RawTerm.hcomp targetSidesPathRaw targetCapRaw)
    rw [sidesPathRawStrengthens, capRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back
      strengthening.injectsBack targetCarrierType carrierSuccess
  rawRenames := by
    cases sidesPathRawRenames
    cases capRawRenames
    rfl

/-- Path-shaped homogeneous composition strengthens by decomposing the
strengthened path carrier for the sides and aligning the cap carrier.

App-pattern: takes `carrierSuccess`, `leftSuccess`, `rightSuccess` as
explicit parameters lifted from the dispatcher's three nested option-
splits on the path carrier type, left endpoint, and right endpoint
respectively.  The body destructures both `sidesPathResult` and
`capResult`, aligns the `Ty.path` shape of `sidesPathType` and the
`carrierType` of the cap, then delegates to
`partialStrengthenTypedHcompPathOfSuccess`.  Extends the recipe from
Phase 39/40/41 (2-option) to 3-option wrappers — the App-pattern
remains uniform: every option-split lifts to a wrapper parameter, the
leaf consumes all witnesses, and soundness mirrors the case cascade. -/
def partialStrengthenTypedHcompPath {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (sidesPathResult : StrengtheningResult strengthening sidesPath)
    (capResult : StrengtheningResult strengthening capValue) :
    StrengtheningResult strengthening
      (Term.hcompPath (context := sourceCtx) modeIsUnivalent
        leftEndpoint rightEndpoint sidesPath capValue) := by
  cases sidesPathResult with
  | mk targetSidesPathType targetSidesPathRaw targetSidesPath
      sidesPathTypeStrengthens sidesPathRawStrengthens
      sidesPathTypeRenames sidesPathRawRenames =>
      have expectedSidesPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint rightEndpoint).partialStrengthen?
              strengthening.back =
            some (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint) := by
        change
          Option.mapThree
            (carrierType.partialStrengthen? strengthening.back)
            (leftEndpoint.partialStrengthen? strengthening.back)
            (rightEndpoint.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
        rw [carrierSuccess, leftSuccess, rightSuccess]
        rfl
      rw [expectedSidesPathTypeStrengthens] at sidesPathTypeStrengthens
      cases sidesPathTypeStrengthens
      cases capResult with
      | mk targetCapType targetCapRaw targetCapValue
          capTypeStrengthens capRawStrengthens capTypeRenames
          capRawRenames =>
          rw [carrierSuccess] at capTypeStrengthens
          cases capTypeStrengthens
          exact partialStrengthenTypedHcompPathOfSuccess
            modeIsUnivalent leftEndpoint rightEndpoint
            targetSidesPath targetCapValue carrierSuccess leftSuccess
            rightSuccess sidesPathRawStrengthens capRawStrengthens
            sidesPathRawRenames capRawRenames

end Term

end LeanFX2
