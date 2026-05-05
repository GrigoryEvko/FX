import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/Suspension

Setoid-level suspension HIT presentation.

The suspension of a source type has two point representatives, `north`
and `south`, and a named meridian relation constructor for each source
value.

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

/-- Setoid-level suspension paths.

The relation has reflexive paths at both endpoints, a meridian from
north to south for every source value, and the symmetric meridian for
the reverse direction.  This is the equivalence closure needed by the
current two-point setoid without erasing the meridian constructor into
`Nonempty`. -/
inductive SuspensionRel (sourceType : Type sourceLevel) :
    SuspensionPoint sourceType → SuspensionPoint sourceType → Prop where
  | reflPath (somePoint : SuspensionPoint sourceType) :
      SuspensionRel sourceType somePoint somePoint
  | meridian (sourceValue : sourceType) :
      SuspensionRel sourceType
        SuspensionPoint.north SuspensionPoint.south
  | meridianSymm (sourceValue : sourceType) :
      SuspensionRel sourceType
        SuspensionPoint.south SuspensionPoint.north

namespace SuspensionRel

/-- Reflexivity for suspension paths. -/
theorem relation_refl {sourceType : Type sourceLevel}
    (someValue : SuspensionPoint sourceType) :
    SuspensionRel sourceType someValue someValue :=
  SuspensionRel.reflPath someValue

/-- Symmetry for suspension paths. -/
theorem relation_symm {sourceType : Type sourceLevel}
    {leftValue rightValue : SuspensionPoint sourceType}
    (relationWitness : SuspensionRel sourceType leftValue rightValue) :
    SuspensionRel sourceType rightValue leftValue := by
  cases relationWitness with
  | reflPath _ => exact SuspensionRel.reflPath leftValue
  | meridian sourceValue => exact SuspensionRel.meridianSymm sourceValue
  | meridianSymm sourceValue => exact SuspensionRel.meridian sourceValue

/-- Transitivity for suspension paths. -/
theorem relation_trans {sourceType : Type sourceLevel}
    {leftValue middleValue rightValue : SuspensionPoint sourceType}
    (firstWitness : SuspensionRel sourceType leftValue middleValue)
    (secondWitness : SuspensionRel sourceType middleValue rightValue) :
    SuspensionRel sourceType leftValue rightValue := by
  cases firstWitness with
  | reflPath _ => exact secondWitness
  | meridian sourceValue =>
      cases secondWitness with
      | reflPath _ => exact SuspensionRel.meridian sourceValue
      | meridianSymm _ => exact SuspensionRel.reflPath SuspensionPoint.north
  | meridianSymm sourceValue =>
      cases secondWitness with
      | reflPath _ => exact SuspensionRel.meridianSymm sourceValue
      | meridian _ => exact SuspensionRel.reflPath SuspensionPoint.south

end SuspensionRel

namespace Suspension

/-- Relation for the setoid-level suspension.

The named relation preserves meridian witnesses instead of collapsing
them to `Nonempty sourceType`. -/
def relation {sourceType : Type sourceLevel}
    (leftValue rightValue : SuspensionPoint sourceType) : Prop :=
  SuspensionRel sourceType leftValue rightValue

/-- Reflexivity of the suspension relation. -/
theorem relation_refl {sourceType : Type sourceLevel}
    (someValue : SuspensionPoint sourceType) :
    Suspension.relation someValue someValue :=
  SuspensionRel.relation_refl someValue

/-- Symmetry of the suspension relation. -/
theorem relation_symm {sourceType : Type sourceLevel}
    {leftValue rightValue : SuspensionPoint sourceType}
    (relationWitness : Suspension.relation leftValue rightValue) :
    Suspension.relation rightValue leftValue :=
  SuspensionRel.relation_symm relationWitness

/-- Transitivity of the suspension relation. -/
theorem relation_trans {sourceType : Type sourceLevel}
    {leftValue middleValue rightValue : SuspensionPoint sourceType}
    (firstWitness : Suspension.relation leftValue middleValue)
    (secondWitness : Suspension.relation middleValue rightValue) :
    Suspension.relation leftValue rightValue :=
  SuspensionRel.relation_trans firstWitness secondWitness

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
  SuspensionRel.meridian sourceValue

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
    | SuspensionRel.reflPath _ => by
        cases leftValue
        · rfl
        · rfl
    | SuspensionRel.meridian sourceValue =>
        meridianRespects sourceValue
    | SuspensionRel.meridianSymm sourceValue =>
        Eq.symm (meridianRespects sourceValue)

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
    | SuspensionRel.reflPath _ => by
        cases leftValue
        · exact HEq.rfl
        · exact HEq.rfl
    | SuspensionRel.meridian sourceValue =>
        meridianRespects sourceValue
    | SuspensionRel.meridianSymm sourceValue =>
        HEq.symm (meridianRespects sourceValue)

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
