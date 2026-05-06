import LeanFX2.Cubical.PathLemmas
import LeanFX2.Reduction.Cumul

/-! # Cubical/Transport

Transport helpers for cubical paths.

## Deliverable

This module names the safe constant-type transport redex shape and
provides its conversion-layer β rule.  The raw and typed parallel
reductions still have transport congruence only; lifting this β rule to
`Step.par` needs a raw preservation lemma for weakened constant path
bodies.
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
raw constant-path recognizer.  This is the exact guard future transport
β should check before reducing. -/
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
This keeps future transport work using the named redex shape through
`ConvCumul`, not just through `Step.par`. -/
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

/-- Conversion-layer β for transport along the named constant type line.

This is the currently safe computation principle for `transp`: it is
restricted to `constantTypeTransport`, so it cannot collapse arbitrary
path lambdas whose bodies mention the interval binder.  A future
`Step.par` β rule needs an additional raw lemma showing that parallel
reduction preserves weakened constant path bodies. -/
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
