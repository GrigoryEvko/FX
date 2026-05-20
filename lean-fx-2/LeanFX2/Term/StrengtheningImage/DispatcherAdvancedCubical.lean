import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.HoTTElimSuccess
import LeanFX2.Term.StrengtheningImage.Binders
import LeanFX2.Term.StrengtheningImage.CubicalComposition
import LeanFX2.Term.StrengtheningImage.EquivIntroAndEffects

/-! # Term/StrengtheningImage/DispatcherAdvancedCubical

Dispatcher-arm soundness for effect, cubical composition, and binder constructors.
-/

namespace LeanFX2

namespace Term

/-- Dispatcher soundness at the `Term.effectPerform` arm.  The arm
threads three Ty witnesses (effect-tag raw, argument carrier, result
carrier) plus two value-level recursive results (operation tag,
arguments).  The `canPerformOperation` predicate is mode/effect-row
metadata that passes through unstrengthened.  The leaf derives the
`effectTagRenames` rename-direction fact from `effectTagSuccess` via
`RawTerm.partialStrengthen?_imp_rename`, then delegates to
`partialStrengthenTypedEffectPerform_sound`. -/
theorem partialStrengthenTyped?_atEffectPerform_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {effectTag : RawTerm sourceScope}
    {effectRow : Effects.EffectRow}
    {operationSignature :
      Effects.OperationSignature (Ty level sourceScope)}
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (operationIH : ∀ operationResult,
        partialStrengthenTyped? operationTag strengthening =
            some operationResult →
          StrengtheningSoundness operationResult)
    (argumentsIH : ∀ argumentsResult,
        partialStrengthenTyped? arguments strengthening =
            some argumentsResult →
          StrengtheningSoundness argumentsResult)
    (result : StrengtheningResult strengthening
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments))
    (success : partialStrengthenTyped?
        (Term.effectPerform (context := sourceCtx) effectTag effectRow
          operationSignature canPerformOperation operationTag arguments)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i targetEffectTag effectTagSuccess
    split at success
    · cases success
    · rename_i targetArgumentCarrier argumentCarrierSuccess
      split at success
      · cases success
      · rename_i targetResultCarrier resultCarrierSuccess
        split at success
        · cases success
        · rename_i operationResult operationRecurse
          split at success
          · cases success
          · rename_i argumentsResult argumentsRecurse
            cases success
            have effectTagRenames :
                effectTag = targetEffectTag.rename strengthening.forward :=
              RawTerm.partialStrengthen?_imp_rename effectTag
                strengthening.forward strengthening.back
                strengthening.injectsBack targetEffectTag effectTagSuccess
            exact partialStrengthenTypedEffectPerform_sound
              effectTag targetEffectTag effectRow operationSignature
              targetArgumentCarrier targetResultCarrier
              canPerformOperation effectTagSuccess
              argumentCarrierSuccess resultCarrierSuccess
              (operationIH operationResult operationRecurse)
              (argumentsIH argumentsResult argumentsRecurse)
              effectTagRenames

/-- Dispatcher soundness at the `Term.glueIntro` arm.  Carries one Ty
witness (baseType), one raw witness (boundaryWitness) under the
cubical mode-univalent flag, plus two value-level IHs (baseValue,
partialValue).  Both value children share the same baseType — partial
glue is the boundary half of the cubical glue type.  Delegates to
`partialStrengthenTypedGlueIntro_sound` which derives both rename
directions internally. -/
theorem partialStrengthenTyped?_atGlueIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseValue strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (partialIH : ∀ partialResult,
        partialStrengthenTyped? partialValue strengthening =
            some partialResult →
          StrengtheningSoundness partialResult)
    (result : StrengtheningResult strengthening
      (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
        boundaryWitness baseValue partialValue))
    (success : partialStrengthenTyped?
        (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
          boundaryWitness baseValue partialValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i targetBaseType baseTypeSuccess
    split at success
    · cases success
    · rename_i targetBoundaryWitness boundarySuccess
      split at success
      · cases success
      · rename_i baseResult baseRecurse
        split at success
        · cases success
        · rename_i partialResult partialRecurse
          cases success
          exact partialStrengthenTypedGlueIntro_sound
            modeIsUnivalent baseType targetBaseType
            boundaryWitness targetBoundaryWitness
            baseTypeSuccess boundarySuccess
            (baseIH baseResult baseRecurse)
            (partialIH partialResult partialRecurse)

/-- Dispatcher soundness at the `Term.pathLam` arm.  Path-lambda is the
first under-binder cubical leaf: the body lives in a context extended
by `Ty.interval`, so the body IH ranges over
`strengthening.lift Ty.interval Ty.interval rfl` strengthening (the
binder shift preserves the interval-typed slot).  Carries 1 Ty
witness (carrier) + 2 raw witnesses (left/right endpoints) +
1 body IH; the wrapper derives all rename directions internally. -/
theorem partialStrengthenTyped?_atPathLam_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (bodyIH : ∀ bodyResult,
        partialStrengthenTyped? body
            (strengthening.lift Ty.interval Ty.interval rfl) =
            some bodyResult →
          StrengtheningSoundness bodyResult)
    (result : StrengtheningResult strengthening
      (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body))
    (success : partialStrengthenTyped?
        (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
          leftEndpoint rightEndpoint body) strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i targetCarrierType carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i bodyResult bodyRecurse
          cases success
          exact partialStrengthenTypedPathLam_sound
            modeIsUnivalent carrierSuccess leftSuccess rightSuccess
            (bodyIH bodyResult bodyRecurse)

/-- Dispatcher soundness at the `Term.lam` arm.  Lam is the first
under-binder leaf whose binder type is itself strengthening-mediated:
the body lives in `sourceCtx.cons domainType`, the strengthened body
must live in `targetCtx.cons targetDomainType`, and the lift uses the
witness `domainSuccess` as a typeclass-style cargo.  The body IH is
therefore quantified over the pair `(targetDomainType, domainSuccess)`
rather than a fixed target — first dispatcher leaf with this shape;
applies again to `lamPi` and any future binder whose argument type is
not closed.  Two Ty witnesses (domain, codomain) thread through; the
wrapper derives both rename directions internally. -/
theorem partialStrengthenTyped?_atLam_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (bodyIH : ∀ targetDomainType
        (domainSuccess :
          domainType.partialStrengthen? strengthening.back =
            some targetDomainType)
        bodyResult,
        partialStrengthenTyped? body
            (strengthening.lift domainType targetDomainType
              domainSuccess) =
            some bodyResult →
          StrengtheningSoundness bodyResult)
    (result : StrengtheningResult strengthening
      (Term.lam (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body))
    (success : partialStrengthenTyped?
        (Term.lam (context := sourceCtx) (domainType := domainType)
          (codomainType := codomainType) body) strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i _ codomainSuccess
      split at success
      · cases success
      · rename_i bodyResult bodyRecurse
        cases success
        exact partialStrengthenTypedLam_sound
          domainSuccess codomainSuccess
          (bodyIH targetDomainType domainSuccess bodyResult
            bodyRecurse)

/-- Dispatcher soundness at the `Term.lamPi` arm.  Dependent-Π lambda
mirrors `lam`'s dependent-lift body-IH shape, but the codomain lives
in `Ty level (sourceScope + 1)` (inside the binder), so no codomain
witness threads through the dispatcher — `partialStrengthenTypedLamPi`
takes only `domainSuccess` and the body result carries the codomain
strengthen-evidence in its `StrengtheningResult`.  Body IH is
quantified over `(targetDomainType, domainSuccess)` because the body
recursion's strengthening (`strengthening.lift domainType
targetDomainType domainSuccess`) depends on the witness. -/
theorem partialStrengthenTyped?_atLamPi_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (bodyIH : ∀ targetDomainType
        (domainSuccess :
          domainType.partialStrengthen? strengthening.back =
            some targetDomainType)
        bodyResult,
        partialStrengthenTyped? body
            (strengthening.lift domainType targetDomainType
              domainSuccess) =
            some bodyResult →
          StrengtheningSoundness bodyResult)
    (result : StrengtheningResult strengthening
      (Term.lamPi (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body))
    (success : partialStrengthenTyped?
        (Term.lamPi (context := sourceCtx) (domainType := domainType)
          (codomainType := codomainType) body) strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i bodyResult bodyRecurse
      cases success
      exact partialStrengthenTypedLamPi_sound
        domainSuccess
        (bodyIH targetDomainType domainSuccess bodyResult
          bodyRecurse)

/-- Dispatcher soundness at the `Term.hcomp` arm.  Cubical homogeneous
composition over a closed-form carrier: both `sidesValue` and
`capValue` live at the same `carrierType`, so the dispatcher carries
no explicit Ty/raw witnesses — the wrapper aligns `capResult`'s
carrier-type strengthening against `sidesResult`'s internally via
`rw [carrierStrengthens] at capTypeStrengthens`.  Mirrors the
two-child-IH shape of glueIntro but without the boundary/witness
threading. -/
theorem partialStrengthenTyped?_atHcomp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sidesIH : ∀ sidesResult,
        partialStrengthenTyped? sidesValue strengthening =
            some sidesResult →
          StrengtheningSoundness sidesResult)
    (capIH : ∀ capResult,
        partialStrengthenTyped? capValue strengthening =
            some capResult →
          StrengtheningSoundness capResult)
    (result : StrengtheningResult strengthening
      (Term.hcomp (context := sourceCtx) (carrierType := carrierType)
        (sidesRaw := sidesRaw) (capRaw := capRaw) modeIsUnivalent
        sidesValue capValue))
    (success : partialStrengthenTyped?
        (Term.hcomp (context := sourceCtx) (carrierType := carrierType)
          (sidesRaw := sidesRaw) (capRaw := capRaw) modeIsUnivalent
          sidesValue capValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i sidesResult sidesRecurse
    split at success
    · cases success
    · rename_i capResult capRecurse
      cases success
      exact partialStrengthenTypedHcomp_sound modeIsUnivalent
        (sidesIH sidesResult sidesRecurse)
        (capIH capResult capRecurse)

/-- Dispatcher soundness at the `Term.hcompPath` arm.  Path-shaped
cubical composition: `sidesPath` lives at `Ty.path carrierType
leftEndpoint rightEndpoint`, so three raw/Ty witnesses thread through
(carrier, left, right), plus two child IHs (sidesPath + capValue).
Mirrors pathLam's 3-witness pattern but at term-level rather than
under a binder.  Wrapper takes both `leftEndpoint`/`rightEndpoint`
explicitly because they are explicit fields of `Term.hcompPath`. -/
theorem partialStrengthenTyped?_atHcompPath_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sidesIH : ∀ sidesPathResult,
        partialStrengthenTyped? sidesPath strengthening =
            some sidesPathResult →
          StrengtheningSoundness sidesPathResult)
    (capIH : ∀ capResult,
        partialStrengthenTyped? capValue strengthening =
            some capResult →
          StrengtheningSoundness capResult)
    (result : StrengtheningResult strengthening
      (Term.hcompPath (context := sourceCtx) (carrierType := carrierType)
        (sidesPathRaw := sidesPathRaw) (capRaw := capRaw)
        modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue))
    (success : partialStrengthenTyped?
        (Term.hcompPath (context := sourceCtx)
          (carrierType := carrierType)
          (sidesPathRaw := sidesPathRaw) (capRaw := capRaw)
          modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i targetCarrierType carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i sidesPathResult sidesRecurse
          split at success
          · cases success
          · rename_i capResult capRecurse
            cases success
            exact partialStrengthenTypedHcompPath_sound
              modeIsUnivalent leftEndpoint rightEndpoint
              carrierSuccess leftSuccess rightSuccess
              (sidesIH sidesPathResult sidesRecurse)
              (capIH capResult capRecurse)

/-- Dispatcher soundness at the `Term.transp` arm.  Heaviest leaf:
cubical transport carries 2 Ty witnesses (sourceType, targetType) +
2 raw witnesses (sourceTypeRaw, targetTypeRaw) + 2 child IHs
(typePath, sourceValue) + metadata (universeLevel, universeLevelLt,
modeIsUnivalent).  Term-level types `sourceType` and `targetType`
are distinct — transp's role is to transport from source to target
along `typePath` — but both still strengthen homogeneously (the
strengthening is a context modification, not a type-shape change). -/
theorem partialStrengthenTyped?_atTransp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pathIH : ∀ pathResult,
        partialStrengthenTyped? typePath strengthening =
            some pathResult →
          StrengtheningSoundness pathResult)
    (sourceIH : ∀ sourceResult,
        partialStrengthenTyped? sourceValue strengthening =
            some sourceResult →
          StrengtheningSoundness sourceResult)
    (result : StrengtheningResult strengthening
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw
        targetTypeRaw typePath sourceValue))
    (success : partialStrengthenTyped?
        (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
          universeLevelLt sourceType targetType sourceTypeRaw
          targetTypeRaw typePath sourceValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  dsimp only [partialStrengthenTyped?] at success
  split at success
  · cases success
  · rename_i targetSourceType sourceTypeSuccess
    split at success
    · cases success
    · rename_i targetTargetType targetTypeSuccess
      split at success
      · cases success
      · rename_i targetSourceTypeRaw sourceTypeRawSuccess
        split at success
        · cases success
        · rename_i targetTargetTypeRaw targetTypeRawSuccess
          split at success
          · cases success
          · rename_i pathResult pathRecurse
            split at success
            · cases success
            · rename_i sourceResult sourceRecurse
              cases success
              exact partialStrengthenTypedTransp_sound modeIsUnivalent
                universeLevel universeLevelLt sourceType targetType
                targetSourceType targetTargetType sourceTypeRaw
                targetTypeRaw targetSourceTypeRaw targetTargetTypeRaw
                sourceTypeSuccess targetTypeSuccess
                sourceTypeRawSuccess targetTypeRawSuccess
                (pathIH pathResult pathRecurse)
                (sourceIH sourceResult sourceRecurse)

end Term

end LeanFX2
