import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/Suspension

Setoid-level suspension HIT presentation.

The suspension of a source type has two point representatives, `north`
and `south`, and a meridian relating them for each source value.  At the
current setoid level, the relation is equality unless the source type is
inhabited; a source witness supplies the meridian and relates the two
points.

This is the 0-truncated presentation.  It does not attempt to encode
higher coherence data for iterated spheres.
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe sourceLevel resultLevel

/-- Point representatives for the suspension of a source type. -/
inductive SuspensionPoint (sourceType : Type sourceLevel) : Type sourceLevel where
  | north : SuspensionPoint sourceType
  | south : SuspensionPoint sourceType

namespace Suspension

/-- Relation for the setoid-level suspension.

Equal points are related.  If the source type is inhabited, a meridian
witness relates all points, including north and south. -/
def relation {sourceType : Type sourceLevel}
    (leftValue rightValue : SuspensionPoint sourceType) : Prop :=
  leftValue = rightValue ∨ Nonempty sourceType

/-- Reflexivity of the suspension relation. -/
theorem relation_refl {sourceType : Type sourceLevel}
    (someValue : SuspensionPoint sourceType) :
    Suspension.relation someValue someValue :=
  Or.inl rfl

/-- Symmetry of the suspension relation. -/
theorem relation_symm {sourceType : Type sourceLevel}
    {leftValue rightValue : SuspensionPoint sourceType}
    (relationWitness : Suspension.relation leftValue rightValue) :
    Suspension.relation rightValue leftValue :=
  match relationWitness with
  | Or.inl equalityWitness => Or.inl (Eq.symm equalityWitness)
  | Or.inr sourceWitness => Or.inr sourceWitness

/-- Transitivity of the suspension relation. -/
theorem relation_trans {sourceType : Type sourceLevel}
    {leftValue middleValue rightValue : SuspensionPoint sourceType}
    (firstWitness : Suspension.relation leftValue middleValue)
    (secondWitness : Suspension.relation middleValue rightValue) :
    Suspension.relation leftValue rightValue :=
  match firstWitness, secondWitness with
  | Or.inl firstEquality, Or.inl secondEquality =>
      Or.inl (Eq.trans firstEquality secondEquality)
  | Or.inr sourceWitness, _ => Or.inr sourceWitness
  | _, Or.inr sourceWitness => Or.inr sourceWitness

/-- Setoid-level suspension presentation. -/
def setoid (sourceType : Type sourceLevel) : HITSetoid.{sourceLevel} :=
  HITSetoid.fromEquivalence
    (SuspensionPoint sourceType)
    Suspension.relation
    Suspension.relation_refl
    Suspension.relation_symm
    Suspension.relation_trans

/-- North representative. -/
def north {sourceType : Type sourceLevel} :
    (Suspension.setoid sourceType).carrier :=
  SuspensionPoint.north

/-- South representative. -/
def south {sourceType : Type sourceLevel} :
    (Suspension.setoid sourceType).carrier :=
  SuspensionPoint.south

/-- A source value supplies a meridian from north to south. -/
theorem meridian {sourceType : Type sourceLevel}
    (sourceValue : sourceType) :
    (Suspension.setoid sourceType).relation
      (Suspension.north (sourceType := sourceType))
      (Suspension.south (sourceType := sourceType)) :=
  Or.inr ⟨sourceValue⟩

/-- Non-dependent recursion out of the setoid-level suspension.

The caller gives cases for north and south plus a proof that every
meridian identifies those case results. -/
def rec {sourceType : Type sourceLevel}
    (resultType : Sort resultLevel)
    (northCase southCase : resultType)
    (meridianRespects : sourceType → northCase = southCase) :
    HITRecursor (Suspension.setoid sourceType) resultType where
  apply := fun
    | SuspensionPoint.north => northCase
    | SuspensionPoint.south => southCase
  respectsRelation := fun {leftValue} {rightValue} relationWitness =>
    match relationWitness with
    | Or.inl equalityWitness => by
        cases equalityWitness
        rfl
    | Or.inr ⟨sourceValue⟩ =>
        match leftValue, rightValue with
        | SuspensionPoint.north, SuspensionPoint.north => rfl
        | SuspensionPoint.north, SuspensionPoint.south =>
            meridianRespects sourceValue
        | SuspensionPoint.south, SuspensionPoint.north =>
            Eq.symm (meridianRespects sourceValue)
        | SuspensionPoint.south, SuspensionPoint.south => rfl

/-- Suspension recursion computes at north by reflexive reduction. -/
theorem rec_north {sourceType : Type sourceLevel}
    (resultType : Sort resultLevel)
    (northCase southCase : resultType)
    (meridianRespects : sourceType → northCase = southCase) :
    (Suspension.rec resultType northCase southCase meridianRespects).run
      (Suspension.north (sourceType := sourceType)) =
      northCase :=
  rfl

/-- Suspension recursion computes at south by reflexive reduction. -/
theorem rec_south {sourceType : Type sourceLevel}
    (resultType : Sort resultLevel)
    (northCase southCase : resultType)
    (meridianRespects : sourceType → northCase = southCase) :
    (Suspension.rec resultType northCase southCase meridianRespects).run
      (Suspension.south (sourceType := sourceType)) =
      southCase :=
  rfl

/-- Suspension recursion respects a meridian witness. -/
theorem rec_meridian {sourceType : Type sourceLevel}
    (resultType : Sort resultLevel)
    (northCase southCase : resultType)
    (meridianRespects : sourceType → northCase = southCase)
    (sourceValue : sourceType) :
    (Suspension.rec resultType northCase southCase meridianRespects).run
      (Suspension.north (sourceType := sourceType)) =
      (Suspension.rec resultType northCase southCase meridianRespects).run
        (Suspension.south (sourceType := sourceType)) :=
  HITRecursor.run_respects
    (Suspension.rec resultType northCase southCase meridianRespects)
    (Suspension.meridian sourceValue)

/-- Dependent induction out of the setoid-level suspension.

The motive is indexed by north/south representatives.  The caller
supplies both point cases plus the heterogeneous computation data for
each meridian. -/
def dependentInductor {sourceType : Type sourceLevel}
    (motive : (Suspension.setoid sourceType).carrier → Sort resultLevel)
    (northCase :
      motive (Suspension.north (sourceType := sourceType)))
    (southCase :
      motive (Suspension.south (sourceType := sourceType)))
    (meridianRespects :
      sourceType → HEq northCase southCase) :
    HITInductor (Suspension.setoid sourceType) motive where
  apply := fun
    | SuspensionPoint.north => northCase
    | SuspensionPoint.south => southCase
  respectsRelation := fun {leftValue} {rightValue} relationWitness =>
    match relationWitness with
    | Or.inl equalityWitness => by
        cases equalityWitness
        exact HEq.rfl
    | Or.inr ⟨sourceValue⟩ =>
        match leftValue, rightValue with
        | SuspensionPoint.north, SuspensionPoint.north => HEq.rfl
        | SuspensionPoint.north, SuspensionPoint.south =>
            meridianRespects sourceValue
        | SuspensionPoint.south, SuspensionPoint.north =>
            HEq.symm (meridianRespects sourceValue)
        | SuspensionPoint.south, SuspensionPoint.south => HEq.rfl

/-- Suspension dependent induction computes at north. -/
theorem dependentInductor_north {sourceType : Type sourceLevel}
    (motive : (Suspension.setoid sourceType).carrier → Sort resultLevel)
    (northCase :
      motive (Suspension.north (sourceType := sourceType)))
    (southCase :
      motive (Suspension.south (sourceType := sourceType)))
    (meridianRespects :
      sourceType → HEq northCase southCase) :
    (Suspension.dependentInductor motive northCase southCase meridianRespects).run
      (Suspension.north (sourceType := sourceType)) =
      northCase :=
  rfl

/-- Suspension dependent induction computes at south. -/
theorem dependentInductor_south {sourceType : Type sourceLevel}
    (motive : (Suspension.setoid sourceType).carrier → Sort resultLevel)
    (northCase :
      motive (Suspension.north (sourceType := sourceType)))
    (southCase :
      motive (Suspension.south (sourceType := sourceType)))
    (meridianRespects :
      sourceType → HEq northCase southCase) :
    (Suspension.dependentInductor motive northCase southCase meridianRespects).run
      (Suspension.south (sourceType := sourceType)) =
      southCase :=
  rfl

/-- Suspension dependent induction respects a meridian witness. -/
theorem dependentInductor_meridian {sourceType : Type sourceLevel}
    (motive : (Suspension.setoid sourceType).carrier → Sort resultLevel)
    (northCase :
      motive (Suspension.north (sourceType := sourceType)))
    (southCase :
      motive (Suspension.south (sourceType := sourceType)))
    (meridianRespects :
      sourceType → HEq northCase southCase)
    (sourceValue : sourceType) :
    HEq
      ((Suspension.dependentInductor
        motive northCase southCase meridianRespects).run
        (Suspension.north (sourceType := sourceType)))
      ((Suspension.dependentInductor
        motive northCase southCase meridianRespects).run
        (Suspension.south (sourceType := sourceType))) :=
  HITInductor.run_respects
    (Suspension.dependentInductor motive northCase southCase meridianRespects)
    (Suspension.meridian sourceValue)

end Suspension

end HIT
end HoTT
end LeanFX2
