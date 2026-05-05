import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/SetTrunc

Setoid-level set truncation presentation.

The current `HITSetoid` foundation tracks point representatives and a
0-dimensional path relation between representatives.  It does not yet
encode higher path constructors, so this module deliberately exposes the
honest setoid-level approximation of set truncation: representatives are
the source values and only reflexively equal representatives are related
by the named `SetTruncRel.reflPath` constructor.

This is not a full higher inductive 0-truncation with a generated
`isSet` constructor for arbitrary source types.  That needs a richer
higher-path presentation than the current setoid layer.
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe sourceLevel resultLevel

/-- The setoid-level path relation for set truncation.

At the current 0-dimensional setoid layer this relation has only a
reflexive path constructor.  It intentionally does not identify
distinct source representatives; the higher `isSet` path constructor is
deferred until the kernel has a higher-path presentation. -/
inductive SetTruncRel (sourceType : Type sourceLevel) :
    sourceType → sourceType → Prop where
  | reflPath (sourceValue : sourceType) :
      SetTruncRel sourceType sourceValue sourceValue

namespace SetTruncRel

/-- Reflexivity for the named set-truncation relation. -/
theorem relation_refl {sourceType : Type sourceLevel}
    (sourceValue : sourceType) :
    SetTruncRel sourceType sourceValue sourceValue :=
  SetTruncRel.reflPath sourceValue

/-- Symmetry for the named set-truncation relation. -/
theorem relation_symm {sourceType : Type sourceLevel}
    {leftValue rightValue : sourceType}
    (relationWitness : SetTruncRel sourceType leftValue rightValue) :
    SetTruncRel sourceType rightValue leftValue := by
  cases relationWitness
  exact SetTruncRel.reflPath leftValue

/-- Transitivity for the named set-truncation relation. -/
theorem relation_trans {sourceType : Type sourceLevel}
    {leftValue middleValue rightValue : sourceType}
    (firstWitness : SetTruncRel sourceType leftValue middleValue)
    (secondWitness : SetTruncRel sourceType middleValue rightValue) :
    SetTruncRel sourceType leftValue rightValue := by
  cases firstWitness
  cases secondWitness
  exact SetTruncRel.reflPath leftValue

end SetTruncRel

/-- Set-truncation presentation at the current setoid level.

The carrier is the source type and the relation has only the reflexive
path constructor.  No distinct point representatives are identified. -/
def SetTrunc (sourceType : Type sourceLevel) : HITSetoid.{sourceLevel} :=
  HITSetoid.fromEquivalence
    sourceType
    (SetTruncRel sourceType)
    SetTruncRel.relation_refl
    SetTruncRel.relation_symm
    SetTruncRel.relation_trans

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
  by
    cases sameValue
    exact SetTruncRel.reflPath leftValue

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

/-- Dependent induction out of the set-truncation presentation.

At the current setoid level, the only relation is equality of source
representatives, so a dependent function over representatives lifts
directly. -/
def dependentInductor {sourceType : Type sourceLevel}
    (motive : (SetTrunc sourceType).carrier → Sort resultLevel)
    (introCase :
      ∀ sourceValue : sourceType,
        motive (SetTrunc.intro sourceValue)) :
    HITInductor (SetTrunc sourceType) motive where
  apply := introCase
  respectsRelation := fun relationWitness => by
    cases relationWitness
    exact HEq.rfl

/-- Set-truncation dependent induction computes on introduced
representatives. -/
theorem dependentInductor_intro {sourceType : Type sourceLevel}
    (motive : (SetTrunc sourceType).carrier → Sort resultLevel)
    (introCase :
      ∀ sourceValue : sourceType,
        motive (SetTrunc.intro sourceValue))
    (sourceValue : sourceType) :
    (SetTrunc.dependentInductor motive introCase).run
      (SetTrunc.intro sourceValue) =
      introCase sourceValue :=
  rfl

/-- Set-truncation dependent induction respects equality paths. -/
theorem dependentInductor_path {sourceType : Type sourceLevel}
    (motive : (SetTrunc sourceType).carrier → Sort resultLevel)
    (introCase :
      ∀ sourceValue : sourceType,
        motive (SetTrunc.intro sourceValue))
    {leftValue rightValue : sourceType}
    (sameValue : leftValue = rightValue) :
    HEq
      ((SetTrunc.dependentInductor motive introCase).run
        (SetTrunc.intro leftValue))
      ((SetTrunc.dependentInductor motive introCase).run
        (SetTrunc.intro rightValue)) :=
  HITInductor.run_respects
    (SetTrunc.dependentInductor motive introCase)
    (SetTrunc.path sameValue)

end SetTrunc

end HIT
end HoTT
end LeanFX2
