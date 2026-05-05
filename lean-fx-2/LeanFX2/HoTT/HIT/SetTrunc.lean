import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/SetTrunc

Setoid-level set truncation presentation.

The current `HITSetoid` foundation tracks point representatives and a
0-dimensional path relation between representatives.  It does not yet
encode higher path constructors, so this module deliberately exposes the
honest setoid-level approximation of set truncation: representatives are
the source values and only equal representatives are related.

This is not a full higher inductive 0-truncation with a generated
`isSet` constructor for arbitrary source types.  That needs a richer
higher-path presentation than the current setoid layer.
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe sourceLevel resultLevel

/-- Set-truncation presentation at the current setoid level.

The carrier is the source type and the relation is equality.  No
distinct point representatives are identified. -/
def SetTrunc (sourceType : Type sourceLevel) : HITSetoid.{sourceLevel} :=
  HITSetoid.discrete sourceType

namespace SetTrunc

/-- Introduce a representative into the set-truncation presentation. -/
def intro {sourceType : Type sourceLevel}
    (sourceValue : sourceType) :
    (SetTrunc sourceType).carrier :=
  sourceValue

/-- Equal source representatives are related in the set-truncation
presentation. -/
theorem path {sourceType : Type sourceLevel}
    {leftValue rightValue : sourceType}
    (sameValue : leftValue = rightValue) :
    (SetTrunc sourceType).relation
      (SetTrunc.intro leftValue)
      (SetTrunc.intro rightValue) :=
  sameValue

/-- Non-dependent recursion out of the set-truncation presentation.

At the current setoid level, the only relation to respect is equality,
so every function out of the source type lifts. -/
def rec {sourceType : Type sourceLevel}
    (resultType : Sort resultLevel)
    (introCase : sourceType → resultType) :
    HITRecursor (SetTrunc sourceType) resultType where
  apply := introCase
  respectsRelation := fun relationWitness => by
    cases relationWitness
    rfl

/-- Set-truncation recursion computes on introduced representatives. -/
theorem rec_intro {sourceType : Type sourceLevel}
    (resultType : Sort resultLevel)
    (introCase : sourceType → resultType)
    (sourceValue : sourceType) :
    (SetTrunc.rec resultType introCase).run
      (SetTrunc.intro sourceValue) =
      introCase sourceValue :=
  rfl

/-- Set-truncation recursion respects equality paths. -/
theorem rec_path {sourceType : Type sourceLevel}
    (resultType : Sort resultLevel)
    (introCase : sourceType → resultType)
    {leftValue rightValue : sourceType}
    (sameValue : leftValue = rightValue) :
    (SetTrunc.rec resultType introCase).run
      (SetTrunc.intro leftValue) =
      (SetTrunc.rec resultType introCase).run
        (SetTrunc.intro rightValue) :=
  HITRecursor.run_respects
    (SetTrunc.rec resultType introCase)
    (SetTrunc.path sameValue)

end SetTrunc

end HIT
end HoTT
end LeanFX2
