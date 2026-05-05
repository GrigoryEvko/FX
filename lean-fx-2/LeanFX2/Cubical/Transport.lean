import LeanFX2.Cubical.PathLemmas

/-! # Cubical/Transport

Transport helpers for cubical paths.

## Deliverable

This module names the safe constant-type transport redex shape.  It
does **not** add a transport computation rule; the raw and typed
parallel reductions still have transport congruence only.  Future
`transpRefl` work should consume this helper instead of matching every
`pathLam` as though it were a constant type line.
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
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    Term context sourceType
      (RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRaw) :=
  Term.transp universeLevel universeLevelLt
    sourceType sourceType typeRaw typeRaw
    (constantTypePath universeLevel universeLevelLt typeCode)
    sourceValue

/-- `constantTypeTransport` projects to exactly the raw transport redex
future `transpRefl` work must handle. -/
theorem constantTypeTransport_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    (constantTypeTransport universeLevel universeLevelLt
      sourceType typeCode sourceValue).toRaw =
      RawTerm.transp (RawTerm.pathLam typeRaw.weaken) sourceRaw :=
  rfl

/-- The type line used by `constantTypeTransport` is accepted by the
raw constant-path recognizer.  This is the exact guard future transport
β should check before reducing. -/
theorem constantTypeTransport_typeLineRecognized
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe universeLevel universeLevelLt) typeRaw) :
    RawTerm.constantPathBody?
      (constantTypePath universeLevel universeLevelLt typeCode).toRaw =
      some typeRaw :=
  constantTypePath_rawRecognized universeLevel universeLevelLt typeCode

/-- The named constant-transport redex is stable under parallel
reduction of its source value.  This is still transport congruence, not
transport β. -/
theorem constantTypeTransport_sourceCong
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
      (constantTypeTransport universeLevel universeLevelLt
        sourceType typeCode sourceValueSource)
      (constantTypeTransport universeLevel universeLevelLt
        sourceType typeCode sourceValueTarget) :=
  Step.par.transp universeLevel universeLevelLt
    sourceType sourceType typeRaw typeRaw
    (Step.par.refl _) sourceStep

/-- Source congruence for the named constant-transport redex projects
through the typed-to-raw bridge to raw transport congruence on the exact
constant type line. -/
theorem constantTypeTransport_sourceCong_toRawBridge
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
        universeLevel universeLevelLt sourceType typeCode sourceStep)

end Cubical
end LeanFX2
