import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.CubicalTransport

/-! # Term/StrengtheningImage/CubicalComposition

Soundness lemmas for cubical homogeneous composition and path-composition wrappers.
-/

namespace LeanFX2

namespace Term

/-- Soundness of `partialStrengthenTypedHcompOfSuccess`: the result's
renamed target term is heterogeneously equal to the original typed
homogeneous composition. -/
theorem partialStrengthenTypedHcompOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {targetSidesValue :
      Term targetCtx targetCarrierType targetSidesRaw}
    {targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw}
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
      capRaw = targetCapRaw.rename strengthening.forward)
    (sidesSound :
      HEq sidesValue
        (Term.rename strengthening.toTermRenaming targetSidesValue))
    (capSound :
      HEq capValue
        (Term.rename strengthening.toTermRenaming targetCapValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedHcompOfSuccess modeIsUnivalent
        (sidesValue := sidesValue) (capValue := capValue)
        targetSidesValue targetCapValue carrierStrengthens
        sidesRawStrengthens capRawStrengthens sidesRawRenames
        capRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedHcompOfSuccess]
  have carrierRenames :
      carrierType = targetCarrierType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierStrengthens
  exact Term.hcomp_HEq_congr modeIsUnivalent carrierRenames
    sidesRawRenames capRawRenames sidesSound capSound

/-- Soundness for the typed homogeneous-composition wrapper.

Mirrors `partialStrengthenTypedHcomp`'s inline-construct pattern:
splits both child results, aligns the cap type via the sides'
carrier-type strengthening, and discharges via `Term.hcomp_HEq_congr`. -/
theorem partialStrengthenTypedHcomp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    {sidesResult : StrengtheningResult strengthening sidesValue}
    {capResult : StrengtheningResult strengthening capValue}
    (sidesSound : StrengtheningSoundness sidesResult)
    (capSound : StrengtheningSoundness capResult) :
    StrengtheningSoundness
      (partialStrengthenTypedHcomp modeIsUnivalent sidesResult
        capResult) := by
  cases sidesResult with
  | mk targetCarrierType targetSidesRaw targetSidesValue
      carrierStrengthens sidesRawStrengthens carrierRenames
      sidesRawRenames =>
      cases capResult with
      | mk targetCapType targetCapRaw targetCapValue capTypeStrengthens
          capRawStrengthens capTypeRenames capRawRenames =>
          rw [carrierStrengthens] at capTypeStrengthens
          cases capTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedHcomp,
              StrengtheningResult.renamedTarget]
            at sidesSound capSound ⊢
          exact Term.hcomp_HEq_congr modeIsUnivalent carrierRenames
            sidesRawRenames capRawRenames sidesSound.termRenames
            capSound.termRenames

/-- Soundness of `partialStrengthenTypedHcompPathOfSuccess`: the
result's renamed target term is heterogeneously equal to the original
typed path-shaped homogeneous composition. -/
theorem partialStrengthenTypedHcompPathOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {targetSidesPath :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetSidesPathRaw}
    {targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
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
      capRaw = targetCapRaw.rename strengthening.forward)
    (sidesPathSound :
      HEq sidesPath
        (Term.rename strengthening.toTermRenaming targetSidesPath))
    (capSound :
      HEq capValue
        (Term.rename strengthening.toTermRenaming targetCapValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedHcompPathOfSuccess modeIsUnivalent
        leftEndpoint rightEndpoint
        (sidesPath := sidesPath) (capValue := capValue)
        targetSidesPath targetCapValue carrierSuccess leftSuccess
        rightSuccess sidesPathRawStrengthens capRawStrengthens
        sidesPathRawRenames capRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedHcompPathOfSuccess]
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
  exact Term.hcompPath_HEq_congr modeIsUnivalent carrierRenames
    leftEndpointRenames rightEndpointRenames sidesPathRawRenames
    capRawRenames sidesPathSound capSound

/-- Soundness of the App-pattern `partialStrengthenTypedHcompPath`
wrapper: destructures both child `StrengtheningResult`s, aligns the
`Ty.path` shape of the sides path's type and the `carrierType` of the
cap, then delegates to `_OfSuccess_sound`.

Mirrors the wrapper's cascade exactly: 3 type/raw witnesses
(`carrierSuccess`/`leftSuccess`/`rightSuccess`) lifted from the
dispatcher to the wrapper become explicit parameters here.  The
`Option.mapThree` shape of the sides path type discharge uses the
same `change`+`rw [carrierSuccess, leftSuccess, rightSuccess]; rfl`
recipe as the wrapper.  Extends the Phase 39/40/41 (2-option) pattern
to 3-option wrappers; child soundness HEqs extracted via
`.termRenames` projection. -/
theorem partialStrengthenTypedHcompPath_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {sidesPathResult : StrengtheningResult strengthening sidesPath}
    {capResult : StrengtheningResult strengthening capValue}
    (sidesPathSound : StrengtheningSoundness sidesPathResult)
    (capSound : StrengtheningSoundness capResult) :
    StrengtheningSoundness
      (partialStrengthenTypedHcompPath modeIsUnivalent leftEndpoint
        rightEndpoint carrierSuccess leftSuccess rightSuccess
        sidesPathResult capResult) := by
  cases sidesPathResult with
  | mk targetSidesPathType targetSidesPathRaw targetSidesPath
      sidesPathTypeStrengthens sidesPathRawStrengthens
      sidesPathTypeRenames sidesPathRawRenames =>
      have expectedSidesPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint
              rightEndpoint).partialStrengthen?
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
          exact partialStrengthenTypedHcompPathOfSuccess_sound
            modeIsUnivalent leftEndpoint rightEndpoint
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (sidesPathRawStrengthens := sidesPathRawStrengthens)
            (capRawStrengthens := capRawStrengthens)
            (sidesPathRawRenames := sidesPathRawRenames)
            (capRawRenames := capRawRenames)
            sidesPathSound.termRenames capSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedPathApp`
wrapper.  Cubical path application: takes the three path-type pivots
(`carrierSuccess`/`leftSuccess`/`rightSuccess`) as wrapper parameters
lifted from the dispatcher.  Mirrors the wrapper's cascade — first
`cases` the `pathResult`, align the `Ty.path` shape via
`Option.mapThree` + `rw + rfl`, then `cases` the `intervalResult`
(which always strengthens to `Ty.interval` trivially since the
strengthening preserves `Ty.interval`), and delegate to
`_OfSuccess_sound`.  Companion of Phase 42's HcompPath soundness:
both ship 3-option-split soundness over the same `Ty.path` pivots,
exercising the App-pattern's uniform scaling across cubical
path-eliminators. -/
theorem partialStrengthenTypedPathApp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {pathResult : StrengtheningResult strengthening pathTerm}
    {intervalResult : StrengtheningResult strengthening intervalTerm}
    (pathSound : StrengtheningSoundness pathResult)
    (intervalSound : StrengtheningSoundness intervalResult) :
    StrengtheningSoundness
      (partialStrengthenTypedPathApp modeIsUnivalent carrierSuccess
        leftSuccess rightSuccess pathResult intervalResult) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPathTerm pathTypeStrengthens
      pathRawStrengthens pathTypeRenames pathRawRenames =>
      have expectedPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint
              rightEndpoint).partialStrengthen?
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
      rw [expectedPathTypeStrengthens] at pathTypeStrengthens
      cases pathTypeStrengthens
      cases intervalResult with
      | mk targetIntervalType targetIntervalRaw targetIntervalTerm
          intervalTypeStrengthens intervalRawStrengthens
          intervalTypeRenames intervalRawRenames =>
          cases intervalTypeStrengthens
          exact partialStrengthenTypedPathAppOfSuccess_sound
            modeIsUnivalent
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (pathRawStrengthens := pathRawStrengthens)
            (intervalRawStrengthens := intervalRawStrengthens)
            (pathRawRenames := pathRawRenames)
            (intervalRawRenames := intervalRawRenames)
            pathSound.termRenames intervalSound.termRenames

end Term

end LeanFX2
