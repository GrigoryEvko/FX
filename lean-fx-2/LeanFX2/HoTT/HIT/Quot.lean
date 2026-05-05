import LeanFX2.HoTT.HIT.Eliminator

/-! # HoTT/HIT/Quot

Quotient HITs as explicit setoid presentations.

This file does not use Lean's quotient type.  A quotient presentation is
an ordinary carrier plus a supplied equivalence relation.  Eliminators
must carry relation-preservation proofs, so the kernel never relies on
`Quot.sound`.

This is intentionally weaker than native quotient syntax: values remain
representatives, and the quotient relation is tracked explicitly.
-/

namespace LeanFX2
namespace HoTT
namespace HIT

universe sourceLevel resultLevel

/-- Quotient HIT presentation over a source type and an explicit
equivalence relation. -/
def QuotientHIT
    (sourceType : Type sourceLevel)
    (relation : sourceType → sourceType → Prop)
    (isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue)
    (isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue)
    (isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue) :
    HITSetoid.{sourceLevel} :=
  HITSetoid.fromEquivalence
    sourceType relation isRefl isSymm isTrans

namespace QuotientHIT

/-- Equality quotient presentation, useful as the smallest smokeable
quotient instance. -/
def equality (sourceType : Type sourceLevel) : HITSetoid.{sourceLevel} :=
  QuotientHIT
    sourceType
    Eq
    (fun sourceValue => Eq.refl sourceValue)
    (fun relationWitness => Eq.symm relationWitness)
    (fun firstWitness secondWitness =>
      Eq.trans firstWitness secondWitness)

/-- Introduce a representative into a quotient presentation. -/
def intro
    {sourceType : Type sourceLevel}
    {relation : sourceType → sourceType → Prop}
    {isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue}
    {isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    (sourceValue : sourceType) :
    (QuotientHIT sourceType relation isRefl isSymm isTrans).carrier :=
  sourceValue

/-- A source-level relation proof becomes a quotient path relation
between introduced representatives. -/
theorem sound
    {sourceType : Type sourceLevel}
    {relation : sourceType → sourceType → Prop}
    {isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue}
    {isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    {leftValue rightValue : sourceType}
    (relationWitness : relation leftValue rightValue) :
    (QuotientHIT sourceType relation isRefl isSymm isTrans).relation
      (QuotientHIT.intro leftValue)
      (QuotientHIT.intro rightValue) :=
  relationWitness

/-- Non-dependent recursion out of a quotient presentation.

The caller supplies a function over representatives plus a proof that
it respects the quotient relation. -/
def rec
    {sourceType : Type sourceLevel}
    {relation : sourceType → sourceType → Prop}
    {isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue}
    {isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    (resultType : Sort resultLevel)
    (introCase : sourceType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        introCase leftValue = introCase rightValue) :
    HITRecursor
      (QuotientHIT sourceType relation isRefl isSymm isTrans)
      resultType where
  apply := introCase
  respectsRelation := relationRespects

/-- Quotient recursion computes on introduced representatives by
reflexive reduction. -/
theorem rec_intro
    {sourceType : Type sourceLevel}
    {relation : sourceType → sourceType → Prop}
    {isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue}
    {isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    (resultType : Sort resultLevel)
    (introCase : sourceType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        introCase leftValue = introCase rightValue)
    (sourceValue : sourceType) :
    (QuotientHIT.rec
      (sourceType := sourceType)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      resultType introCase relationRespects).run
      (QuotientHIT.intro sourceValue) =
      introCase sourceValue :=
  rfl

/-- Recursion maps related representatives to equal outputs. -/
theorem rec_sound
    {sourceType : Type sourceLevel}
    {relation : sourceType → sourceType → Prop}
    {isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue}
    {isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    (resultType : Sort resultLevel)
    (introCase : sourceType → resultType)
    (relationRespects :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        introCase leftValue = introCase rightValue)
    {leftValue rightValue : sourceType}
    (relationWitness : relation leftValue rightValue) :
    (QuotientHIT.rec
      (sourceType := sourceType)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      resultType introCase relationRespects).run
      (QuotientHIT.intro leftValue) =
      (QuotientHIT.rec
        (sourceType := sourceType)
        (relation := relation)
        (isRefl := isRefl)
        (isSymm := isSymm)
        (isTrans := isTrans)
        resultType introCase relationRespects).run
        (QuotientHIT.intro rightValue) :=
  HITRecursor.run_respects
    (QuotientHIT.rec
      (sourceType := sourceType)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      resultType introCase relationRespects)
    (QuotientHIT.sound relationWitness)

/-- Constant recursion out of a quotient presentation. -/
def recConstant
    {sourceType : Type sourceLevel}
    {relation : sourceType → sourceType → Prop}
    {isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue}
    {isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    (resultType : Sort resultLevel)
    (resultValue : resultType) :
    HITRecursor
      (QuotientHIT sourceType relation isRefl isSymm isTrans)
      resultType :=
  HITRecursor.constant resultType resultValue

/-- Constant quotient recursion computes by reflexive reduction. -/
theorem recConstant_intro
    {sourceType : Type sourceLevel}
    {relation : sourceType → sourceType → Prop}
    {isRefl : ∀ sourceValue : sourceType,
      relation sourceValue sourceValue}
    {isSymm :
      ∀ {leftValue rightValue : sourceType},
        relation leftValue rightValue →
        relation rightValue leftValue}
    {isTrans :
      ∀ {leftValue middleValue rightValue : sourceType},
        relation leftValue middleValue →
        relation middleValue rightValue →
        relation leftValue rightValue}
    (resultType : Sort resultLevel)
    (resultValue : resultType)
    (sourceValue : sourceType) :
    (QuotientHIT.recConstant
      (sourceType := sourceType)
      (relation := relation)
      (isRefl := isRefl)
      (isSymm := isSymm)
      (isTrans := isTrans)
      resultType resultValue).run
      (QuotientHIT.intro sourceValue) =
      resultValue :=
  rfl

end QuotientHIT

end HIT
end HoTT
end LeanFX2
