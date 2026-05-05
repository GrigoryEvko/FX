import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/Coequalizer

Setoid-level coequalizer HIT presentation.

A coequalizer of parallel maps `leftMap rightMap : sourceType →
targetType` has target representatives and path constructors
identifying `leftMap sourceValue` with `rightMap sourceValue`.

This module does not synthesize the equivalence closure of those path
constructors.  Callers provide the relation, the equivalence proofs, and
the map-equality witnesses directly.  This keeps the presentation
zero-axiom and avoids Lean's quotient primitives.
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe sourceLevel targetLevel resultLevel

/-- Explicit setoid presentation of a coequalizer. -/
def CoequalizerHIT
    (sourceType : Type sourceLevel)
    (targetType : Type targetLevel)
    (leftMap : sourceType → targetType)
    (rightMap : sourceType → targetType)
    (relation : targetType → targetType → Prop)
    (isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue)
    (isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue)
    (isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue)
    (equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)) :
    HITSetoid.{targetLevel} :=
  let _equalizeRespects := equalizeRespects
  HITSetoid.fromEquivalence targetType relation isRefl isSymm isTrans

namespace CoequalizerHIT

/-- Introduce a target representative into the coequalizer. -/
def point
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (targetValue : targetType) :
    (CoequalizerHIT sourceType targetType leftMap rightMap
      relation isRefl isSymm isTrans equalizeRespects).carrier :=
  targetValue

/-- Path witness equating the two maps at one source representative. -/
theorem equalize
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (sourceValue : sourceType) :
    (CoequalizerHIT sourceType targetType leftMap rightMap
      relation isRefl isSymm isTrans equalizeRespects).relation
      (CoequalizerHIT.point (leftMap sourceValue))
      (CoequalizerHIT.point (rightMap sourceValue)) :=
  equalizeRespects sourceValue

/-- Non-dependent recursion out of a coequalizer presentation. -/
def rec
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (resultType : Sort resultLevel)
    (targetCase : targetType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        targetCase leftValue = targetCase rightValue) :
    HITRecursor
      (CoequalizerHIT sourceType targetType leftMap rightMap
        relation isRefl isSymm isTrans equalizeRespects)
      resultType where
  apply := targetCase
  respectsRelation := relationRespects

/-- Coequalizer recursion computes on point representatives. -/
theorem rec_point
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (resultType : Sort resultLevel)
    (targetCase : targetType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        targetCase leftValue = targetCase rightValue)
    (targetValue : targetType) :
    (CoequalizerHIT.rec
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (equalizeRespects := equalizeRespects)
      resultType targetCase relationRespects).run
      (CoequalizerHIT.point targetValue) =
      targetCase targetValue :=
  rfl

/-- Coequalizer recursion respects the path equating the two maps. -/
theorem rec_equalize
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (resultType : Sort resultLevel)
    (targetCase : targetType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        targetCase leftValue = targetCase rightValue)
    (sourceValue : sourceType) :
    (CoequalizerHIT.rec
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (equalizeRespects := equalizeRespects)
      resultType targetCase relationRespects).run
      (CoequalizerHIT.point (leftMap sourceValue)) =
      (CoequalizerHIT.rec
        (sourceType := sourceType)
        (leftMap := leftMap)
        (rightMap := rightMap)
        (relation := relation)
        (isRefl := isRefl)
        (isSymm := isSymm)
        (isTrans := isTrans)
        (equalizeRespects := equalizeRespects)
        resultType targetCase relationRespects).run
        (CoequalizerHIT.point (rightMap sourceValue)) :=
  HITRecursor.run_respects
    (CoequalizerHIT.rec
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (equalizeRespects := equalizeRespects)
      resultType targetCase relationRespects)
    (CoequalizerHIT.equalize sourceValue)

/-- Dependent induction out of a coequalizer presentation. -/
def dependentInductor
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (motive :
      (CoequalizerHIT sourceType targetType leftMap rightMap
        relation isRefl isSymm isTrans equalizeRespects).carrier →
        Sort resultLevel)
    (targetCase :
      ∀ targetValue : targetType,
        motive (CoequalizerHIT.point targetValue))
    (relationRespects :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        HEq (targetCase leftValue) (targetCase rightValue)) :
    HITInductor
      (CoequalizerHIT sourceType targetType leftMap rightMap
        relation isRefl isSymm isTrans equalizeRespects)
      motive where
  apply := targetCase
  respectsRelation := relationRespects

/-- Coequalizer dependent induction computes on point representatives. -/
theorem dependentInductor_point
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (motive :
      (CoequalizerHIT sourceType targetType leftMap rightMap
        relation isRefl isSymm isTrans equalizeRespects).carrier →
        Sort resultLevel)
    (targetCase :
      ∀ targetValue : targetType,
        motive (CoequalizerHIT.point targetValue))
    (relationRespects :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        HEq (targetCase leftValue) (targetCase rightValue))
    (targetValue : targetType) :
    (CoequalizerHIT.dependentInductor
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (equalizeRespects := equalizeRespects)
      motive targetCase relationRespects).run
      (CoequalizerHIT.point targetValue) =
      targetCase targetValue :=
  rfl

/-- Coequalizer dependent induction respects the path equating the two
maps. -/
theorem dependentInductor_equalize
    {sourceType : Type sourceLevel}
    {targetType : Type targetLevel}
    {leftMap : sourceType → targetType}
    {rightMap : sourceType → targetType}
    {relation : targetType → targetType → Prop}
    {isRefl :
      ∀ targetValue : targetType,
        relation targetValue targetValue}
    {isSymm :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : targetType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {equalizeRespects :
      ∀ sourceValue : sourceType,
        relation (leftMap sourceValue) (rightMap sourceValue)}
    (motive :
      (CoequalizerHIT sourceType targetType leftMap rightMap
        relation isRefl isSymm isTrans equalizeRespects).carrier →
        Sort resultLevel)
    (targetCase :
      ∀ targetValue : targetType,
        motive (CoequalizerHIT.point targetValue))
    (relationRespects :
      ∀ {leftValue rightValue : targetType},
        relation leftValue rightValue →
        HEq (targetCase leftValue) (targetCase rightValue))
    (sourceValue : sourceType) :
    HEq
      ((CoequalizerHIT.dependentInductor
        (sourceType := sourceType)
        (leftMap := leftMap)
        (rightMap := rightMap)
        (relation := relation)
        (isRefl := isRefl)
        (isSymm := isSymm)
        (isTrans := isTrans)
        (equalizeRespects := equalizeRespects)
        motive targetCase relationRespects).run
        (CoequalizerHIT.point (leftMap sourceValue)))
      ((CoequalizerHIT.dependentInductor
        (sourceType := sourceType)
        (leftMap := leftMap)
        (rightMap := rightMap)
        (relation := relation)
        (isRefl := isRefl)
        (isSymm := isSymm)
        (isTrans := isTrans)
        (equalizeRespects := equalizeRespects)
        motive targetCase relationRespects).run
        (CoequalizerHIT.point (rightMap sourceValue))) :=
  HITInductor.run_respects
    (CoequalizerHIT.dependentInductor
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (equalizeRespects := equalizeRespects)
      motive targetCase relationRespects)
    (CoequalizerHIT.equalize sourceValue)

end CoequalizerHIT

end HIT
end HoTT
end LeanFX2
