import LeanFX2.Bridge
import LeanFX2.Bridge.IdEqType
import LeanFX2.Bridge.PathIdInverse
import LeanFX2.Bridge.PathIdMeta
import LeanFX2.Bridge.PathEqType
import LeanFX2.Cubical.Bridge
import LeanFX2.Cubical.Transport
import LeanFX2.Cubical.Ua
import LeanFX2.Translation.CubicalToObservational
import LeanFX2.Translation.ObservationalToCubical
import LeanFX2.Translation.Inverse
import LeanFX2.Tools.DependencyAudit

/-! # Smoke/Bridge — typed↔raw roundtrip examples.

```lean
-- toRaw of a built Term recovers via rfl
example (i : Fin scope) :
    (Term.var (ctx := ctx) i).toRaw = RawTerm.var i := rfl

-- toRaw of β-redex recovers raw β-redex
example :
    (Term.app (Term.lam body) arg).toRaw = RawTerm.app (RawTerm.lam body.toRaw) arg.toRaw := rfl

-- typed Step.par lifts to raw RawStep.par via the bridge
example {parallelStep : Step.par t1 t2} (biW : Step.par.isBi parallelStep) :
    RawStep.par t1.toRaw t2.toRaw :=
  Step.par.toRawBridge parallelStep biW
```

## Critical edge case: refl-bearing β-redex

```lean
-- This SHOULD work in lean-fx-2 (where it doesn't in lean-fx)
example {arg : Term ctx ty argRaw} :
    (Term.app
      (Term.lam (Term.refl (RawTerm.var ⟨0, _⟩))) arg).toRaw
    = RawTerm.app (RawTerm.lam (RawTerm.refl (RawTerm.var ⟨0, _⟩))) argRaw := rfl

-- After β-reduction, the typed substitute matches raw substitute:
-- typed:  Term.refl argRaw   (after subst, refl's witness is argRaw)
-- raw:    RawTerm.refl argRaw  (singleton substitution puts argRaw at pos 0)
-- Both match because Subst.singleton.forRaw = RawTermSubst.singleton (arg.toRaw)
```

## Dependencies

* `Bridge.lean`

## Implementation plan (Layer 14)

1. toRaw round-trip on each Term ctor
2. Bridge on simple β-redex
3. Bridge on refl-bearing β-redex (the LOAD-BEARING test)
4. Bridge on idJ-bearing β-redex
-/

namespace LeanFX2.Smoke

/-- Typed path application must project to the exact raw path-app shape. -/
theorem pathApp_toRaw_smoke {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint intervalRaw : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    (Term.pathApp
      modeIsUnivalent
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
        bodyTerm)
      intervalTerm).toRaw =
      RawTerm.pathApp (RawTerm.pathLam bodyRaw) intervalRaw := rfl

/-- Typed path β must bridge to the raw `betaPathApp` target, not merely
to some raw congruence fallback. -/
theorem betaPathApp_toRawBridge_smoke {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
    {intervalRawSource intervalRawTarget : RawTerm scope}
    {bodySource :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
    {intervalSource : Term context Ty.interval intervalRawSource}
    {intervalTarget : Term context Ty.interval intervalRawTarget}
    (bodyStep : Step.par bodySource bodyTarget)
    (intervalStep : Step.par intervalSource intervalTarget) :
    RawStep.par
      (RawTerm.pathApp (RawTerm.pathLam bodyRawSource) intervalRawSource)
      (bodyRawTarget.subst0 intervalRawTarget) :=
  Step.par.toRawBridge
    (Step.par.betaPathApp
      modeIsUnivalent
      (leftEndpoint := leftEndpoint)
      (rightEndpoint := rightEndpoint)
      bodyStep intervalStep)

/-- Deep typed path β must bridge to the raw deep path β rule. -/
theorem betaPathAppDeep_toRawBridge_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRawSource intervalRawSource intervalRawTarget : RawTerm scope}
    {bodyRawTarget : RawTerm (scope + 1)}
    {pathSource :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawSource}
    {bodyTarget :
      Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
    {intervalSource : Term context Ty.interval intervalRawSource}
    {intervalTarget : Term context Ty.interval intervalRawTarget}
    (pathStep :
      Step.par pathSource
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
          bodyTarget))
    (intervalStep : Step.par intervalSource intervalTarget) :
    RawStep.par
      (RawTerm.pathApp pathRawSource intervalRawSource)
      (bodyRawTarget.subst0 intervalRawTarget) :=
  Step.par.toRawBridge
    (Step.par.betaPathAppDeep modeIsUnivalent pathStep intervalStep)

/-- Typed Glue β must bridge to the raw `betaGlueElimIntro` target. -/
theorem betaGlueElimIntro_toRawBridge_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm scope}
    {baseSource : Term context baseType baseRawSource}
    {baseTarget : Term context baseType baseRawTarget}
    {partialSource : Term context baseType partialRawSource}
    {partialTarget : Term context baseType partialRawTarget}
    (baseStep : Step.par baseSource baseTarget)
    (partialStep : Step.par partialSource partialTarget) :
    RawStep.par
      (RawTerm.glueElim
        (RawTerm.glueIntro baseRawSource partialRawSource))
      baseRawTarget :=
  Step.par.toRawBridge
    (Step.par.betaGlueElimIntro
      modeIsUnivalent
      (boundaryWitness := boundaryWitness) baseStep partialStep)

/-- Deep typed Glue β must bridge to the raw deep Glue β rule. -/
theorem betaGlueElimIntroDeep_toRawBridge_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRawSource baseRawTarget partialRawTarget :
      RawTerm scope}
    {gluedSource :
      Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
    {baseTarget : Term context baseType baseRawTarget}
    {partialTarget : Term context baseType partialRawTarget}
    (gluedStep :
      Step.par gluedSource
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseTarget partialTarget)) :
    RawStep.par (RawTerm.glueElim gluedRawSource) baseRawTarget :=
  Step.par.toRawBridge
    (Step.par.betaGlueElimIntroDeep modeIsUnivalent gluedStep)

/-- Typed transport congruence currently has only cong parity; this smoke
locks that parity to the raw transport congruence rule. -/
theorem transpCong_toRawBridge_smoke {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {universeLevel : UniverseLevel}
    {universeLevelLt : universeLevel.toNat + 1 ≤ level}
    {sourceType targetType : Ty level scope}
    {sourceTypeRaw targetTypeRaw : RawTerm scope}
    {pathRawSource pathRawTarget sourceRawSource sourceRawTarget :
      RawTerm scope}
    {pathSource :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawSource}
    {pathTarget :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRawTarget}
    {sourceTerm : Term context sourceType sourceRawSource}
    {targetTerm : Term context sourceType sourceRawTarget}
    (pathStep : Step.par pathSource pathTarget)
    (sourceStep : Step.par sourceTerm targetTerm) :
    RawStep.par
      (RawTerm.transp pathRawSource sourceRawSource)
      (RawTerm.transp pathRawTarget sourceRawTarget) :=
  Step.par.toRawBridge
    (Step.par.transp modeIsUnivalent universeLevel universeLevelLt
      sourceType targetType sourceTypeRaw targetTypeRaw pathStep sourceStep)

/-- Constant-type transport wiring smoke.

This theorem intentionally composes the guardrail pieces that keep future
transport computation honest: typed constant type paths, the raw
constant-path recognizer, typed transport congruence, the typed-to-raw
bridge, `ConvCumul` congruence, and the conversion-layer constant
transport β rule. -/
theorem constantTypeTransport_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {universeLevel : UniverseLevel}
    {universeLevelLt : universeLevel.toNat + 1 ≤ level}
    {sourceType : Ty level scope}
    {typeRaw sourceRawSource sourceRawTarget : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    {sourceValueSource : Term context sourceType sourceRawSource}
    {sourceValueTarget : Term context sourceType sourceRawTarget}
    (sourceStep : Step.par sourceValueSource sourceValueTarget)
    (sourceRel : ConvCumul sourceValueSource sourceValueTarget) :
    And
      (RawTerm.constantPathBody?
        (Cubical.constantTypePath modeIsUnivalent
          universeLevel universeLevelLt typeCode).toRaw =
          some typeRaw)
      (And
        (Step.par
          (Cubical.constantTypeTransport modeIsUnivalent
            universeLevel universeLevelLt
            sourceType typeCode sourceValueSource)
          (Cubical.constantTypeTransport modeIsUnivalent
            universeLevel universeLevelLt
            sourceType typeCode sourceValueTarget))
        (And
          (RawStep.par
            (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRawSource)
            (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRawTarget))
          (And
            (ConvCumul
              (Cubical.constantTypeTransport modeIsUnivalent
                universeLevel universeLevelLt
                sourceType typeCode sourceValueSource)
              (Cubical.constantTypeTransport modeIsUnivalent
                universeLevel universeLevelLt
                sourceType typeCode sourceValueTarget))
            (ConvCumul
              (Cubical.constantTypeTransport modeIsUnivalent
                universeLevel universeLevelLt
                sourceType typeCode sourceValueSource)
              sourceValueSource)))) := by
  exact And.intro
    (Cubical.constantTypeTransport_typeLineRecognized
      modeIsUnivalent universeLevel universeLevelLt typeCode)
    (And.intro
      (Cubical.constantTypeTransport_sourceCong
        modeIsUnivalent universeLevel universeLevelLt sourceType typeCode
        sourceStep)
      (And.intro
        (Cubical.constantTypeTransport_sourceCong_toRawBridge
          modeIsUnivalent universeLevel universeLevelLt sourceType typeCode
          sourceStep)
        (And.intro
          (Cubical.constantTypeTransport_sourceConvCumul
            modeIsUnivalent universeLevel universeLevelLt sourceType typeCode
            sourceRel)
          (Cubical.constantTypeTransport_betaConvCumul
            modeIsUnivalent universeLevel universeLevelLt sourceType typeCode
            sourceValueSource))))

/-- Typed hcomp congruence currently has only cong parity; this smoke
locks that parity to the raw hcomp congruence rule. -/
theorem hcompCong_toRawBridge_smoke {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRawSource sidesRawTarget capRawSource capRawTarget :
      RawTerm scope}
    {sidesSource : Term context carrierType sidesRawSource}
    {sidesTarget : Term context carrierType sidesRawTarget}
    {capSource : Term context carrierType capRawSource}
    {capTarget : Term context carrierType capRawTarget}
    (sidesStep : Step.par sidesSource sidesTarget)
    (capStep : Step.par capSource capTarget) :
    RawStep.par
      (RawTerm.hcomp sidesRawSource capRawSource)
      (RawTerm.hcomp sidesRawTarget capRawTarget) :=
  Step.par.toRawBridge
    (Step.par.hcomp modeIsUnivalent sidesStep capStep)

/-- Path/id bridge wiring smoke.

This compiles only if the typed cubical constant-path constructor, typed
identity reflexivity constructor, the raw projections, and both bridge modules
agree on the same endpoint raw index. -/
theorem constantPathIdBridge_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    And
      ((Bridge.constantPathToId modeIsUnivalent pointTerm
        (Cubical.constantPath modeIsUnivalent pointTerm)).toRaw =
          RawTerm.refl pointRaw)
      (And
        ((Bridge.reflIdToConstantPath modeIsUnivalent pointTerm
          (Term.refl carrierType pointRaw)).toRaw =
            RawTerm.pathLam pointRaw.weaken)
        (And
          ((Bridge.reflIdToConstantPath modeIsUnivalent pointTerm
            (Bridge.constantPathToId modeIsUnivalent pointTerm
              (Cubical.constantPath modeIsUnivalent pointTerm))).toRaw =
              RawTerm.pathLam pointRaw.weaken)
          ((Bridge.constantPathToId modeIsUnivalent pointTerm
            (Bridge.reflIdToConstantPath modeIsUnivalent pointTerm
              (Term.refl carrierType pointRaw))).toRaw =
              RawTerm.refl pointRaw))) := by
  exact And.intro
    (Bridge.constantPathToId_toRaw modeIsUnivalent pointTerm
      (Cubical.constantPath modeIsUnivalent pointTerm))
    (And.intro
      (Bridge.reflIdToConstantPath_toRaw modeIsUnivalent pointTerm
        (Term.refl carrierType pointRaw))
      (And.intro
        (Bridge.constantPath_roundTrip_toRaw modeIsUnivalent pointTerm)
        (Bridge.reflId_roundTrip_toRaw modeIsUnivalent pointTerm)))

/-- Observational type-equality bridge wiring smoke.

This checks that the bridge-facing `IdEqType` names consume both the
reflexive and heterogeneous univalence reductions rather than leaving the
module as a documentation-only shell. -/
theorem idEqTypeBridge_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness :
      Term context (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    And
      (Conv (Term.equivReflIdAtId (context := context)
          innerLevel innerLevelLt carrier carrierRaw)
        (Term.equivReflId (context := context) carrier))
      (Conv (Term.uaIntroHet (context := context)
          innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness)
        equivWitness) :=
  And.intro
    (Bridge.idEqTypeRefl innerLevel innerLevelLt carrier carrierRaw)
    (Bridge.idEqTypeHet innerLevel innerLevelLt
      carrierARaw carrierBRaw equivWitness)

/-- Cubical type-path/equivalence bridge wiring smoke.

This checks the honest rfl fragment: a canonical constant type path in the
universe produces the canonical identity equivalence for an explicit carrier.
-/
theorem pathEqTypeBridge_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw) :
    And
      ((Bridge.constantTypePathToEquivRefl modeIsUnivalent
        innerLevel innerLevelLt
        carrier typeCode
        (Cubical.constantTypePath modeIsUnivalent
          innerLevel innerLevelLt typeCode)).toRaw =
          (Term.equivReflId (context := context) carrier).toRaw)
      (Bridge.constantTypePathToEquivRefl modeIsUnivalent
        innerLevel innerLevelLt
        carrier typeCode
        (Cubical.constantTypePath modeIsUnivalent
          innerLevel innerLevelLt typeCode) =
          Term.equivReflId carrier) :=
  And.intro
    (Bridge.constantTypePathToEquivRefl_toRaw modeIsUnivalent
      innerLevel innerLevelLt
      carrier typeCode
      (Cubical.constantTypePath modeIsUnivalent
        innerLevel innerLevelLt typeCode))
    (Bridge.constantTypePathToEquivRefl_onCanonical modeIsUnivalent
      innerLevel innerLevelLt
      carrier typeCode)

/-- Cubical-facing bridge façade smoke.

This exercises `Cubical.Bridge` names rather than the underlying
`Bridge.*` names, so the cubical bridge module is load-bearing in the import
surface. -/
theorem cubicalBridgeFacade_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    And
      ((Cubical.constantPathToObservationalId modeIsUnivalent pointTerm
        (Cubical.constantPath modeIsUnivalent pointTerm)).toRaw =
          RawTerm.refl pointRaw)
      ((Cubical.observationalReflToConstantPath modeIsUnivalent pointTerm
        (Term.refl carrierType pointRaw)).toRaw =
          RawTerm.pathLam pointRaw.weaken) :=
  And.intro
    (Cubical.constantPathToObservationalId_toRaw modeIsUnivalent pointTerm
      (Cubical.constantPath modeIsUnivalent pointTerm))
    (Cubical.observationalReflToConstantPath_toRaw modeIsUnivalent pointTerm
      (Term.refl carrierType pointRaw))

/-- Cubical-facing type-path/equivalence façade smoke. -/
theorem cubicalTypeBridgeFacade_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw) :
    Cubical.constantCubicalTypePathToEquiv modeIsUnivalent
      innerLevel innerLevelLt carrier typeCode
      (Cubical.constantTypePath modeIsUnivalent
        innerLevel innerLevelLt typeCode) =
      Term.equivReflId carrier :=
  Cubical.constantCubicalTypePathToEquiv_onCanonical
    modeIsUnivalent innerLevel innerLevelLt carrier typeCode

/-- Type-level cubical-to-observational translation smoke. -/
theorem cubicalToObservationalTy_fullStackWiring_smoke
    {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint boundaryWitness : RawTerm scope) :
    And
      (Translation.cubicalToObservationalTy Ty.interval =
        (Ty.unit (level := level) (scope := scope)))
      (And
        (Translation.cubicalToObservationalTy
          (Ty.path carrier leftEndpoint rightEndpoint) =
            Ty.id (Translation.cubicalToObservationalTy carrier)
              leftEndpoint rightEndpoint)
        (Translation.cubicalToObservationalTy
          (Ty.glue carrier boundaryWitness) =
            Translation.cubicalToObservationalTy carrier)) :=
  And.intro
    Translation.cubicalToObservationalTy_interval
    (And.intro
      (Translation.cubicalToObservationalTy_path
        carrier leftEndpoint rightEndpoint)
      (Translation.cubicalToObservationalTy_glue
        carrier boundaryWitness))

/-- Type-level observational-to-cubical translation smoke. -/
theorem observationalToCubicalTy_fullStackWiring_smoke
    {level scope : Nat}
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope) :
    And
      (Translation.observationalToCubicalTy
        (Ty.id carrier leftEndpoint rightEndpoint) =
          Ty.path (Translation.observationalToCubicalTy carrier)
            leftEndpoint rightEndpoint)
      (And
        (Translation.observationalToCubicalTy
          (Ty.oeq carrier leftEndpoint rightEndpoint) =
            Ty.path (Translation.observationalToCubicalTy carrier)
              leftEndpoint rightEndpoint)
        (Translation.observationalToCubicalTy
          (Ty.idStrict carrier leftEndpoint rightEndpoint) =
            Ty.path (Translation.observationalToCubicalTy carrier)
              leftEndpoint rightEndpoint)) :=
  And.intro
    (Translation.observationalToCubicalTy_id
      carrier leftEndpoint rightEndpoint)
    (And.intro
      (Translation.observationalToCubicalTy_oeq
        carrier leftEndpoint rightEndpoint)
      (Translation.observationalToCubicalTy_idStrict
        carrier leftEndpoint rightEndpoint))

/-- Type-level translation inverse smoke on the supported `Unit` carrier
fragment. -/
theorem translationInverseTy_fullStackWiring_smoke
    {level scope : Nat}
    (leftEndpoint rightEndpoint : RawTerm scope) :
    And
      (Translation.cubicalToObservationalTy
        (Translation.observationalToCubicalTy
          (Ty.id (Ty.unit (level := level) (scope := scope))
            leftEndpoint rightEndpoint)) =
          Ty.id Ty.unit leftEndpoint rightEndpoint)
      (Translation.observationalToCubicalTy
        (Translation.cubicalToObservationalTy
          (Ty.path (Ty.unit (level := level) (scope := scope))
            leftEndpoint rightEndpoint)) =
          Ty.path Ty.unit leftEndpoint rightEndpoint) :=
  And.intro
    (Translation.observationalCubicalRoundTripTy_id
      Ty.unit leftEndpoint rightEndpoint
      Translation.observationalCubicalRoundTripTy_unit)
    (Translation.cubicalObservationalRoundTripTy_path
      Ty.unit leftEndpoint rightEndpoint
      Translation.cubicalObservationalRoundTripTy_unit)

/-- Set-level Path/Id equivalence computes as identity in both directions. -/
theorem pathIdEquivMeta_fullStackWiring_smoke :
    And
      ((Bridge.pathIdEquivMeta (true : Bool) true).toFun (Path.refl true) =
        (rfl : true = true))
      ((Bridge.pathIdEquivMeta (true : Bool) true).invFun
        (rfl : true = true) = Path.refl true) :=
  And.intro rfl rfl

/-- Cubical `ua` facade smoke for the reflexive kernel conversion. -/
theorem cubicalUaReflConv_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Conv (Term.equivReflIdAtId (context := context)
        innerLevel innerLevelLt carrier carrierRaw)
      (Term.equivReflId (context := context) carrier) :=
  Cubical.uaReflConv innerLevel innerLevelLt carrier carrierRaw

/-- Cubical `ua_beta` facade smoke at the reflexive meta fragment. -/
theorem cubicalUaBetaMetaRefl_fullStackWiring_smoke
    (leftValue : Bool) :
    (Eq.refl Bool) ▸ leftValue
      = (Univalence.idToEquivMeta (Eq.refl Bool)).toFun leftValue :=
  Cubical.uaBetaMetaRefl Bool leftValue

#assert_no_axioms LeanFX2.Smoke.pathApp_toRaw_smoke
#assert_no_axioms LeanFX2.Smoke.betaPathApp_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.betaPathAppDeep_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.betaGlueElimIntro_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.betaGlueElimIntroDeep_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.transpCong_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.constantTypeTransport_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.hcompCong_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.constantPathIdBridge_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.idEqTypeBridge_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.pathEqTypeBridge_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.cubicalBridgeFacade_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.cubicalTypeBridgeFacade_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.cubicalToObservationalTy_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.observationalToCubicalTy_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.translationInverseTy_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.pathIdEquivMeta_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.cubicalUaReflConv_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.cubicalUaBetaMetaRefl_fullStackWiring_smoke

end LeanFX2.Smoke
