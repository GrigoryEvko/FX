import LeanFX2.Bridge
import LeanFX2.Bridge.PathIdInverse
import LeanFX2.Cubical.Transport
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
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint intervalRaw : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    (Term.pathApp
      (Term.pathLam carrierType leftEndpoint rightEndpoint bodyTerm)
      intervalTerm).toRaw =
      RawTerm.pathApp (RawTerm.pathLam bodyRaw) intervalRaw := rfl

/-- Typed path β must bridge to the raw `betaPathApp` target, not merely
to some raw congruence fallback. -/
theorem betaPathApp_toRawBridge_smoke {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
      (leftEndpoint := leftEndpoint)
      (rightEndpoint := rightEndpoint)
      bodyStep intervalStep)

/-- Deep typed path β must bridge to the raw deep path β rule. -/
theorem betaPathAppDeep_toRawBridge_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodyTarget))
    (intervalStep : Step.par intervalSource intervalTarget) :
    RawStep.par
      (RawTerm.pathApp pathRawSource intervalRawSource)
      (bodyRawTarget.subst0 intervalRawTarget) :=
  Step.par.toRawBridge (Step.par.betaPathAppDeep pathStep intervalStep)

/-- Typed Glue β must bridge to the raw `betaGlueElimIntro` target. -/
theorem betaGlueElimIntro_toRawBridge_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
      (boundaryWitness := boundaryWitness) baseStep partialStep)

/-- Deep typed Glue β must bridge to the raw deep Glue β rule. -/
theorem betaGlueElimIntroDeep_toRawBridge_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRawSource baseRawTarget partialRawTarget :
      RawTerm scope}
    {gluedSource :
      Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
    {baseTarget : Term context baseType baseRawTarget}
    {partialTarget : Term context baseType partialRawTarget}
    (gluedStep :
      Step.par gluedSource
        (Term.glueIntro baseType boundaryWitness baseTarget partialTarget)) :
    RawStep.par (RawTerm.glueElim gluedRawSource) baseRawTarget :=
  Step.par.toRawBridge
    (Step.par.betaGlueElimIntroDeep gluedStep)

/-- Typed transport congruence currently has only cong parity; this smoke
locks that parity to the raw transport congruence rule. -/
theorem transpCong_toRawBridge_smoke {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
    (Step.par.transp universeLevel universeLevelLt
      sourceType targetType sourceTypeRaw targetTypeRaw pathStep sourceStep)

/-- Constant-type transport wiring smoke.

This theorem intentionally composes the guardrail pieces that keep future
transport computation honest: typed constant type paths, the raw
constant-path recognizer, typed transport congruence, the typed-to-raw
bridge, and `ConvCumul` congruence.  It is still a congruence smoke, not
a transport β rule. -/
theorem constantTypeTransport_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
        (Cubical.constantTypePath universeLevel universeLevelLt typeCode).toRaw =
          some typeRaw)
      (And
        (Step.par
          (Cubical.constantTypeTransport universeLevel universeLevelLt
            sourceType typeCode sourceValueSource)
          (Cubical.constantTypeTransport universeLevel universeLevelLt
            sourceType typeCode sourceValueTarget))
        (And
          (RawStep.par
            (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRawSource)
            (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRawTarget))
          (ConvCumul
            (Cubical.constantTypeTransport universeLevel universeLevelLt
              sourceType typeCode sourceValueSource)
            (Cubical.constantTypeTransport universeLevel universeLevelLt
              sourceType typeCode sourceValueTarget)))) := by
  exact And.intro
    (Cubical.constantTypeTransport_typeLineRecognized
      universeLevel universeLevelLt typeCode)
    (And.intro
      (Cubical.constantTypeTransport_sourceCong
        universeLevel universeLevelLt sourceType typeCode
        sourceStep)
      (And.intro
        (Cubical.constantTypeTransport_sourceCong_toRawBridge
          universeLevel universeLevelLt sourceType typeCode
          sourceStep)
        (Cubical.constantTypeTransport_sourceConvCumul
          universeLevel universeLevelLt sourceType typeCode
          sourceRel)))

/-- Typed hcomp congruence currently has only cong parity; this smoke
locks that parity to the raw hcomp congruence rule. -/
theorem hcompCong_toRawBridge_smoke {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
  Step.par.toRawBridge (Step.par.hcomp sidesStep capStep)

/-- Path/id bridge wiring smoke.

This compiles only if the typed cubical constant-path constructor, typed
identity reflexivity constructor, the raw projections, and both bridge modules
agree on the same endpoint raw index. -/
theorem constantPathIdBridge_fullStackWiring_smoke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    And
      ((Bridge.constantPathToId pointTerm
        (Cubical.constantPath pointTerm)).toRaw =
          RawTerm.refl pointRaw)
      (And
        ((Bridge.reflIdToConstantPath pointTerm
          (Term.refl carrierType pointRaw)).toRaw =
            RawTerm.pathLam pointRaw.weaken)
        (And
          ((Bridge.reflIdToConstantPath pointTerm
            (Bridge.constantPathToId pointTerm
              (Cubical.constantPath pointTerm))).toRaw =
              RawTerm.pathLam pointRaw.weaken)
          ((Bridge.constantPathToId pointTerm
            (Bridge.reflIdToConstantPath pointTerm
              (Term.refl carrierType pointRaw))).toRaw =
              RawTerm.refl pointRaw))) := by
  exact And.intro
    (Bridge.constantPathToId_toRaw pointTerm (Cubical.constantPath pointTerm))
    (And.intro
      (Bridge.reflIdToConstantPath_toRaw pointTerm
        (Term.refl carrierType pointRaw))
      (And.intro
        (Bridge.constantPath_roundTrip_toRaw pointTerm)
        (Bridge.reflId_roundTrip_toRaw pointTerm)))

#assert_no_axioms LeanFX2.Smoke.pathApp_toRaw_smoke
#assert_no_axioms LeanFX2.Smoke.betaPathApp_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.betaPathAppDeep_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.betaGlueElimIntro_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.betaGlueElimIntroDeep_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.transpCong_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.constantTypeTransport_fullStackWiring_smoke
#assert_no_axioms LeanFX2.Smoke.hcompCong_toRawBridge_smoke
#assert_no_axioms LeanFX2.Smoke.constantPathIdBridge_fullStackWiring_smoke

end LeanFX2.Smoke
