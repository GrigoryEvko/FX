import LeanFX2.Cubical.PathLemmas
import LeanFX2.Reduction.Cumul.Relation.Inductive
import LeanFX2.Reduction.ParStar

/-! # Cubical/Transport

Transport helpers for cubical paths.

## Deliverable

This module names the safe constant-type transport redex shape and
provides its β rule at the conversion layer (`ConvCumul`) AND at the
parallel-step layer (`Step.par`).  The raw preservation lemma
`RawStep.par.weaken_inv` (Phase G.0, `Reduction/RawParWeakenInv.lean`)
unblocks the par lift; the matching typed ctor
`Step.par.transpReflBeta` (`Reduction/ParRed.lean`) closes the
shallow shape.

## Root status

* Layer: typed-derived
* Load-bearing for: Smoke/Bridge, Smoke/AuditPhase12A2Day2, Smoke/AuditPhase12A2D254
* Axiom budget: zero (verified via `#assert_no_axioms` in Tools/AuditAll/)
-/

namespace LeanFX2
namespace Cubical

/-- Transport along a recognized constant type line.

The source and target carriers are intentionally the same typed
`sourceType`, and the type path is specifically `constantTypePath`.
This constructs the redex shape for future constant-transport β without
granting that β rule yet. -/
def constantTypeTransport {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    Term context sourceType
      (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRaw) :=
  Term.transp modeIsUnivalent universeLevel universeLevelLt
    sourceType sourceType typeRaw typeRaw
    (constantTypePath modeIsUnivalent universeLevel universeLevelLt typeCode)
    sourceValue

/-- `constantTypeTransport` projects to exactly the raw transport redex
future `transpRefl` work must handle. -/
theorem constantTypeTransport_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
      sourceType typeCode sourceValue).toRaw =
      RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRaw :=
  rfl

/-- The type line used by `constantTypeTransport` is accepted by the
raw constant-path recognizer.  This is the guard the cd-cascade
`cdTranspCase` consults before firing β; the recognizer answer drives
`unweaken?` which selects between `transpReflBetaDeep` and `transpCong`
in `RawCdDominates`. -/
theorem constantTypeTransport_typeLineRecognized
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw) :
    RawTerm.constantPathBody?
      (constantTypePath modeIsUnivalent universeLevel universeLevelLt typeCode).toRaw =
      some typeRaw :=
  constantTypePath_rawRecognized modeIsUnivalent universeLevel universeLevelLt typeCode

/-- The named constant-transport redex is stable under parallel
reduction of its source value.  This is still transport congruence, not
transport β. -/
theorem constantTypeTransport_sourceCong
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRawSource sourceRawTarget : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    {sourceValueSource : Term context sourceType sourceRawSource}
    {sourceValueTarget : Term context sourceType sourceRawTarget}
    (sourceStep : Step.par sourceValueSource sourceValueTarget) :
    Step.par
      (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
        sourceType typeCode sourceValueSource)
      (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
        sourceType typeCode sourceValueTarget) :=
  Step.par.transp modeIsUnivalent universeLevel universeLevelLt
    sourceType sourceType typeRaw typeRaw
    (Step.par.refl _) sourceStep

/-- Source congruence for the named constant-transport redex projects
through the typed-to-raw bridge to raw transport congruence on the exact
constant type line. -/
theorem constantTypeTransport_sourceCong_toRawBridge
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRawSource sourceRawTarget : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    {sourceValueSource : Term context sourceType sourceRawSource}
    {sourceValueTarget : Term context sourceType sourceRawTarget}
    (sourceStep : Step.par sourceValueSource sourceValueTarget) :
    RawStep.par
      (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRawSource)
      (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRawTarget) := by
  simpa [constantTypeTransport_toRaw]
    using Step.par.toRawBridge
      (constantTypeTransport_sourceCong
        modeIsUnivalent universeLevel universeLevelLt sourceType typeCode sourceStep)

/-- Conversion-level congruence for the named constant-transport redex.
Mirrors `_sourceCong` at the `ConvCumul` layer.  Companion β rules
(`_betaConvCumul`, `_betaParStep`, `_betaParStar`) close the named-redex
β principle across all three reduction layers. -/
theorem constantTypeTransport_sourceConvCumul
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRawSource sourceRawTarget : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    {sourceValueSource : Term context sourceType sourceRawSource}
    {sourceValueTarget : Term context sourceType sourceRawTarget}
    (sourceRel : ConvCumul sourceValueSource sourceValueTarget) :
    ConvCumul
      (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
        sourceType typeCode sourceValueSource)
      (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
        sourceType typeCode sourceValueTarget) :=
  ConvCumul.transpCong modeIsUnivalent universeLevel universeLevelLt
    sourceType sourceType typeRaw typeRaw
    (ConvCumul.refl _) sourceRel

/-- Parallel-step β for transport along the named constant type line.

The named-redex `constantTypeTransport ... typeCode sourceValue`
parallel-reduces to `sourceValue` in one step.  This is the
`Step.par`-level analog of `constantTypeTransport_betaConvCumul`,
unblocked by `RawStep.par.weaken_inv` (Phase G.0) and the matching
typed ctor `Step.par.transpReflBeta` (Phase G).  Earlier versions
of this module had to defer this lift; the deferral is now
discharged. -/
theorem constantTypeTransport_betaParStep
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    Step.par
      (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
        sourceType typeCode sourceValue)
      sourceValue :=
  Step.par.transpReflBeta modeIsUnivalent universeLevel universeLevelLt
    sourceType
    (constantTypePath modeIsUnivalent universeLevel universeLevelLt typeCode)
    (Step.par.refl sourceValue)

/-- The β step at `Step.par` projects through the typed-to-raw bridge
to the raw β fact: `RawTerm.transp (pathLam typeRaw.weaken) sourceRaw`
parallel-reduces to `sourceRaw`.  Mirrors `_sourceCong_toRawBridge`'s
shape — the bridge gives a raw witness consumers needing only raw
parallel reduction can call directly. -/
theorem constantTypeTransport_betaParStep_toRawBridge
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    RawStep.par
      (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRaw)
      sourceRaw := by
  simpa [constantTypeTransport_toRaw]
    using Step.par.toRawBridge
      (constantTypeTransport_betaParStep modeIsUnivalent universeLevel
        universeLevelLt sourceType typeCode sourceValue)

/-- Multistep parallel β for transport along the named constant type
line.  Lifts `constantTypeTransport_betaParStep` to the reflexive-
transitive closure used by `Conv`.  This is the form callers reach
for when they need a `Step.parStar` witness (the underlying relation
of `Conv` after Phase 6 confluence).

One-line corollary: `Step.par.toStar` lifts the single par-step. -/
theorem constantTypeTransport_betaParStar
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    Step.parStar
      (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
        sourceType typeCode sourceValue)
      sourceValue :=
  Step.par.toStar
    (constantTypeTransport_betaParStep modeIsUnivalent universeLevel
      universeLevelLt sourceType typeCode sourceValue)

/-- Conversion-layer β for transport along the named constant type line.

This is the safe computation principle for `transp` at conversion
level: it is restricted to `constantTypeTransport`, so it cannot
collapse arbitrary path lambdas whose bodies mention the interval
binder.  Companion `constantTypeTransport_betaParStep` lifts the
same principle to `Step.par` directly; `_betaParStar` lifts further
to the reflexive-transitive closure. -/
theorem constantTypeTransport_betaConvCumul
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    ConvCumul
      (constantTypeTransport modeIsUnivalent universeLevel universeLevelLt
        sourceType typeCode sourceValue)
      sourceValue :=
  ConvCumul.betaTranspConstantTypeCumul modeIsUnivalent
    universeLevel universeLevelLt sourceType
    (constantTypePath modeIsUnivalent universeLevel universeLevelLt typeCode)
    sourceValue

end Cubical
end LeanFX2
