import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/Pushout

Setoid-level pushout HIT presentation.

A pushout of `leftMap : sourceType → leftType` and
`rightMap : sourceType → rightType` has representatives from either
side and seam paths identifying `leftMap sourceValue` with
`rightMap sourceValue`.

This module does not synthesize the equivalence closure of those seam
paths.  Instead, callers provide the relation and equivalence proofs,
plus the seam relation witnesses.  This keeps the kernel zero-axiom and
prevents hidden quotient machinery.
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe sourceLevel leftLevel rightLevel resultLevel

/-- Carrier representatives for a pushout presentation. -/
def PushoutCarrier
    (leftType : Type leftLevel)
    (rightType : Type rightLevel) :
    Type (max leftLevel rightLevel) :=
  Sum leftType rightType

/-- Explicit setoid presentation of a pushout.

The relation is supplied rather than generated internally.  The
`glueRespects` argument records that each source value gives a seam
between the corresponding left and right representatives. -/
def PushoutHIT
    (sourceType : Type sourceLevel)
    (leftType : Type leftLevel)
    (rightType : Type rightLevel)
    (leftMap : sourceType → leftType)
    (rightMap : sourceType → rightType)
    (relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop)
    (isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue)
    (isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue)
    (isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue)
    (glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))) :
    HITSetoid.{max leftLevel rightLevel} :=
  let _glueRespects := glueRespects
  HITSetoid.fromEquivalence
    (PushoutCarrier leftType rightType)
    relation isRefl isSymm isTrans

namespace PushoutHIT

/-- Evaluate a pushout representative by case analysis on its side. -/
def evaluate
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {resultType : Sort resultLevel}
    (leftCase : leftType → resultType)
    (rightCase : rightType → resultType) :
    PushoutCarrier leftType rightType → resultType
  | Sum.inl leftValue => leftCase leftValue
  | Sum.inr rightValue => rightCase rightValue

/-- Evaluate a dependent pushout branch by case analysis on its side. -/
def dependentEvaluate
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    (motive : PushoutCarrier leftType rightType → Sort resultLevel)
    (leftCase :
      ∀ leftValue : leftType,
        motive (Sum.inl leftValue))
    (rightCase :
      ∀ rightValue : rightType,
        motive (Sum.inr rightValue)) :
    (pushoutValue : PushoutCarrier leftType rightType) →
      motive pushoutValue
  | Sum.inl leftValue => leftCase leftValue
  | Sum.inr rightValue => rightCase rightValue

/-- Introduce a left representative into the pushout. -/
def left
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (leftValue : leftType) :
    (PushoutHIT sourceType leftType rightType leftMap rightMap
      relation isRefl isSymm isTrans glueRespects).carrier :=
  Sum.inl leftValue

/-- Introduce a right representative into the pushout. -/
def right
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (rightValue : rightType) :
    (PushoutHIT sourceType leftType rightType leftMap rightMap
      relation isRefl isSymm isTrans glueRespects).carrier :=
  Sum.inr rightValue

/-- Seam relation witness for a source value. -/
theorem glue
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (sourceValue : sourceType) :
    (PushoutHIT sourceType leftType rightType leftMap rightMap
      relation isRefl isSymm isTrans glueRespects).relation
      (PushoutHIT.left (leftMap sourceValue))
      (PushoutHIT.right (rightMap sourceValue)) :=
  glueRespects sourceValue

/-- Non-dependent recursion out of a pushout presentation.

The caller supplies cases for both sides plus a proof that the whole
provided relation is respected. -/
def rec
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (resultType : Sort resultLevel)
    (leftCase : leftType → resultType)
    (rightCase : rightType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        PushoutHIT.evaluate leftCase rightCase leftValue =
        PushoutHIT.evaluate leftCase rightCase rightValue) :
    HITRecursor
      (PushoutHIT sourceType leftType rightType leftMap rightMap
        relation isRefl isSymm isTrans glueRespects)
      resultType where
  apply := PushoutHIT.evaluate leftCase rightCase
  respectsRelation := relationRespects

/-- Pushout recursion computes on left representatives. -/
theorem rec_left
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (resultType : Sort resultLevel)
    (leftCase : leftType → resultType)
    (rightCase : rightType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        PushoutHIT.evaluate leftCase rightCase leftValue =
        PushoutHIT.evaluate leftCase rightCase rightValue)
    (leftValue : leftType) :
    (PushoutHIT.rec
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (glueRespects := glueRespects)
      resultType leftCase rightCase relationRespects).run
      (Sum.inl leftValue) =
      leftCase leftValue :=
  rfl

/-- Pushout recursion computes on right representatives. -/
theorem rec_right
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (resultType : Sort resultLevel)
    (leftCase : leftType → resultType)
    (rightCase : rightType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        PushoutHIT.evaluate leftCase rightCase leftValue =
        PushoutHIT.evaluate leftCase rightCase rightValue)
    (rightValue : rightType) :
    (PushoutHIT.rec
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (glueRespects := glueRespects)
      resultType leftCase rightCase relationRespects).run
      (Sum.inr rightValue) =
      rightCase rightValue :=
  rfl

/-- Pushout recursion respects a glue seam. -/
theorem rec_glue
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (resultType : Sort resultLevel)
    (leftCase : leftType → resultType)
    (rightCase : rightType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        PushoutHIT.evaluate leftCase rightCase leftValue =
        PushoutHIT.evaluate leftCase rightCase rightValue)
    (sourceValue : sourceType) :
    (PushoutHIT.rec
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (glueRespects := glueRespects)
      resultType leftCase rightCase relationRespects).run
      (Sum.inl (leftMap sourceValue)) =
      (PushoutHIT.rec
        (sourceType := sourceType)
        (leftMap := leftMap)
        (rightMap := rightMap)
        (relation := relation)
        (isRefl := isRefl)
        (isSymm := isSymm)
        (isTrans := isTrans)
        (glueRespects := glueRespects)
        resultType leftCase rightCase relationRespects).run
        (Sum.inr (rightMap sourceValue)) :=
  HITRecursor.run_respects
    (PushoutHIT.rec
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (glueRespects := glueRespects)
      resultType leftCase rightCase relationRespects)
    (PushoutHIT.glue sourceValue)

/-- Dependent induction out of a pushout presentation.

The caller supplies representative cases for both sides and a
heterogeneous proof that the provided pushout relation is respected. -/
def dependentInductor
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (motive :
      (PushoutHIT sourceType leftType rightType leftMap rightMap
        relation isRefl isSymm isTrans glueRespects).carrier →
        Sort resultLevel)
    (leftCase :
      ∀ leftValue : leftType,
        motive (Sum.inl leftValue))
    (rightCase :
      ∀ rightValue : rightType,
        motive (Sum.inr rightValue))
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        HEq
          (PushoutHIT.dependentEvaluate motive leftCase rightCase leftValue)
          (PushoutHIT.dependentEvaluate motive leftCase rightCase rightValue)) :
    HITInductor
      (PushoutHIT sourceType leftType rightType leftMap rightMap
        relation isRefl isSymm isTrans glueRespects)
      motive where
  apply := PushoutHIT.dependentEvaluate motive leftCase rightCase
  respectsRelation := relationRespects

/-- Pushout dependent induction computes on left representatives. -/
theorem dependentInductor_left
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (motive :
      (PushoutHIT sourceType leftType rightType leftMap rightMap
        relation isRefl isSymm isTrans glueRespects).carrier →
        Sort resultLevel)
    (leftCase :
      ∀ leftValue : leftType,
        motive (Sum.inl leftValue))
    (rightCase :
      ∀ rightValue : rightType,
        motive (Sum.inr rightValue))
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        HEq
          (PushoutHIT.dependentEvaluate motive leftCase rightCase leftValue)
          (PushoutHIT.dependentEvaluate motive leftCase rightCase rightValue))
    (leftValue : leftType) :
    (PushoutHIT.dependentInductor
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (glueRespects := glueRespects)
      motive leftCase rightCase relationRespects).run
      (Sum.inl leftValue) =
      leftCase leftValue :=
  rfl

/-- Pushout dependent induction computes on right representatives. -/
theorem dependentInductor_right
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (motive :
      (PushoutHIT sourceType leftType rightType leftMap rightMap
        relation isRefl isSymm isTrans glueRespects).carrier →
        Sort resultLevel)
    (leftCase :
      ∀ leftValue : leftType,
        motive (Sum.inl leftValue))
    (rightCase :
      ∀ rightValue : rightType,
        motive (Sum.inr rightValue))
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        HEq
          (PushoutHIT.dependentEvaluate motive leftCase rightCase leftValue)
          (PushoutHIT.dependentEvaluate motive leftCase rightCase rightValue))
    (rightValue : rightType) :
    (PushoutHIT.dependentInductor
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (glueRespects := glueRespects)
      motive leftCase rightCase relationRespects).run
      (Sum.inr rightValue) =
      rightCase rightValue :=
  rfl

/-- Pushout dependent induction respects a glue witness. -/
theorem dependentInductor_glue
    {sourceType : Type sourceLevel}
    {leftType : Type leftLevel}
    {rightType : Type rightLevel}
    {leftMap : sourceType → leftType}
    {rightMap : sourceType → rightType}
    {relation :
      PushoutCarrier leftType rightType →
      PushoutCarrier leftType rightType →
      Prop}
    {isRefl :
      ∀ pushoutValue : PushoutCarrier leftType rightType,
        relation pushoutValue pushoutValue}
    {isSymm :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {glueRespects :
      ∀ sourceValue : sourceType,
        relation
          (Sum.inl (leftMap sourceValue))
          (Sum.inr (rightMap sourceValue))}
    (motive :
      (PushoutHIT sourceType leftType rightType leftMap rightMap
        relation isRefl isSymm isTrans glueRespects).carrier →
        Sort resultLevel)
    (leftCase :
      ∀ leftValue : leftType,
        motive (Sum.inl leftValue))
    (rightCase :
      ∀ rightValue : rightType,
        motive (Sum.inr rightValue))
    (relationRespects :
      ∀ {leftValue rightValue : PushoutCarrier leftType rightType},
        relation leftValue rightValue →
        HEq
          (PushoutHIT.dependentEvaluate motive leftCase rightCase leftValue)
          (PushoutHIT.dependentEvaluate motive leftCase rightCase rightValue))
    (sourceValue : sourceType) :
    HEq
      ((PushoutHIT.dependentInductor
        (sourceType := sourceType)
        (leftMap := leftMap)
        (rightMap := rightMap)
        (relation := relation)
        (isRefl := isRefl)
        (isSymm := isSymm)
        (isTrans := isTrans)
        (glueRespects := glueRespects)
        motive leftCase rightCase relationRespects).run
        (Sum.inl (leftMap sourceValue)))
      ((PushoutHIT.dependentInductor
        (sourceType := sourceType)
        (leftMap := leftMap)
        (rightMap := rightMap)
        (relation := relation)
        (isRefl := isRefl)
        (isSymm := isSymm)
        (isTrans := isTrans)
        (glueRespects := glueRespects)
        motive leftCase rightCase relationRespects).run
        (Sum.inr (rightMap sourceValue))) :=
  HITInductor.run_respects
    (PushoutHIT.dependentInductor
      (sourceType := sourceType)
      (leftMap := leftMap)
      (rightMap := rightMap)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      (glueRespects := glueRespects)
      motive leftCase rightCase relationRespects)
    (PushoutHIT.glue sourceValue)

end PushoutHIT

end HIT
end HoTT
end LeanFX2
