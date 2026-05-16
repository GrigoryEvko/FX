import LeanFX2.Term.ContextStrengthening

/-! # Typed partial strengthening.

This module is the typed-term reconstruction layer above
`RawTerm.partialStrengthen?`, `Ty.partialStrengthen?`, and
`ContextStrengthening`.

The first exported artifact is `Term.StrengtheningResult`: a target
typed term together with the exact type/raw strengthening successes and
the forward renaming equations.  The constructors below cover the
closed atomic terms and the variable case; recursive constructors are
added in later files against the same result type.
-/

namespace LeanFX2

namespace Term

/-- Result of successfully strengthening a typed source term through a
context-strengthening morphism.

The target term is first-class data.  The `typeStrengthens` and
`rawStrengthens` fields say the target indices are exactly the results
computed by the type/raw partial-strengthening functions.  The
`typeRenames` and `rawRenames` fields are the semantic soundness facts:
renaming the target term's indices forward recovers the source indices.
-/
structure StrengtheningResult {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sourceTerm : Term sourceCtx sourceType sourceRaw) where
  targetType : Ty level targetScope
  targetRaw : RawTerm targetScope
  targetTerm : Term targetCtx targetType targetRaw
  typeStrengthens :
    sourceType.partialStrengthen? strengthening.back = some targetType
  rawStrengthens :
    sourceRaw.partialStrengthen? strengthening.back = some targetRaw
  typeRenames : sourceType = targetType.rename strengthening.forward
  rawRenames : sourceRaw = targetRaw.rename strengthening.forward

namespace StrengtheningResult

/-- The target term renamed through the strengthening's forward morphism
has the source context.  The source type/raw equalities are carried in
`typeRenames` and `rawRenames`; consumers can cast with those facts when
they need syntactic equality to the original source term. -/
def renamedTarget {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (result : StrengtheningResult strengthening sourceTerm) :
    Term sourceCtx
      (result.targetType.rename strengthening.forward)
      (result.targetRaw.rename strengthening.forward) :=
  Term.rename strengthening.toTermRenaming result.targetTerm

end StrengtheningResult

/-- Typed partial strengthening for a surviving variable.  This is the
first load-bearing case: the raw variable must survive the partial
renaming, and the context morphism supplies the exact target variable
type. -/
def partialStrengthenTypedVarOfSurvives {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sourcePosition : Fin sourceScope)
    (targetPosition : Fin targetScope)
    (survives : strengthening.back sourcePosition = some targetPosition) :
    StrengtheningResult strengthening
      (Term.var (context := sourceCtx) sourcePosition) where
  targetType := varType targetCtx targetPosition
  targetRaw := RawTerm.var targetPosition
  targetTerm := Term.var (context := targetCtx) targetPosition
  typeStrengthens :=
    strengthening.varTypeStrengthens sourcePosition targetPosition survives
  rawStrengthens := by
    change
      (match strengthening.back sourcePosition with
      | some targetPosition => some (RawTerm.var targetPosition)
      | none => none) = some (RawTerm.var targetPosition)
    rw [survives]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename
      (varType sourceCtx sourcePosition)
      strengthening.forward strengthening.back strengthening.injectsBack
      (varType targetCtx targetPosition)
      (strengthening.varTypeStrengthens sourcePosition targetPosition
        survives)
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.var sourcePosition)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.var targetPosition)
      (by
        change
          (match strengthening.back sourcePosition with
          | some targetPosition => some (RawTerm.var targetPosition)
          | none => none) = some (RawTerm.var targetPosition)
        rw [survives])

/-- Closed unit terms strengthen through every context strengthening. -/
def partialStrengthenTypedUnit {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningResult strengthening (Term.unit (context := sourceCtx)) where
  targetType := Ty.unit
  targetRaw := RawTerm.unit
  targetTerm := Term.unit (context := targetCtx)
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- Closed `true` terms strengthen through every context strengthening. -/
def partialStrengthenTypedBoolTrue {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningResult strengthening (Term.boolTrue (context := sourceCtx)) where
  targetType := Ty.bool
  targetRaw := RawTerm.boolTrue
  targetTerm := Term.boolTrue (context := targetCtx)
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- Closed `false` terms strengthen through every context strengthening. -/
def partialStrengthenTypedBoolFalse {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningResult strengthening (Term.boolFalse (context := sourceCtx)) where
  targetType := Ty.bool
  targetRaw := RawTerm.boolFalse
  targetTerm := Term.boolFalse (context := targetCtx)
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- Closed natural-zero terms strengthen through every context strengthening. -/
def partialStrengthenTypedNatZero {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningResult strengthening (Term.natZero (context := sourceCtx)) where
  targetType := Ty.nat
  targetRaw := RawTerm.natZero
  targetTerm := Term.natZero (context := targetCtx)
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- Closed interval-zero terms strengthen through every context strengthening. -/
def partialStrengthenTypedInterval0 {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningResult strengthening (Term.interval0 (context := sourceCtx)) where
  targetType := Ty.interval
  targetRaw := RawTerm.interval0
  targetTerm := Term.interval0 (context := targetCtx)
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- Closed interval-one terms strengthen through every context strengthening. -/
def partialStrengthenTypedInterval1 {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningResult strengthening (Term.interval1 (context := sourceCtx)) where
  targetType := Ty.interval
  targetRaw := RawTerm.interval1
  targetTerm := Term.interval1 (context := targetCtx)
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- List-nil strengthens when its element type strengthens. -/
def partialStrengthenTypedListNilOfType {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningResult strengthening
      (Term.listNil (context := sourceCtx) (elementType := elementType)) where
  targetType := Ty.listType targetElementType
  targetRaw := RawTerm.listNil
  targetTerm := Term.listNil (context := targetCtx)
    (elementType := targetElementType)
  typeStrengthens := by
    change
      (match elementType.partialStrengthen? strengthening.back with
      | some strengthenedElementType =>
          some (Ty.listType strengthenedElementType)
      | none => none) = some (Ty.listType targetElementType)
    rw [elementTypeStrengthens]
  rawStrengthens := rfl
  typeRenames := by
    exact Ty.partialStrengthen?_imp_rename
      (Ty.listType elementType)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.listType targetElementType)
      (by
        change
          (match elementType.partialStrengthen? strengthening.back with
          | some strengthenedElementType =>
              some (Ty.listType strengthenedElementType)
          | none => none) = some (Ty.listType targetElementType)
        rw [elementTypeStrengthens])
  rawRenames := rfl

/-- Option-none strengthens when its element type strengthens. -/
def partialStrengthenTypedOptionNoneOfType {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningResult strengthening
      (Term.optionNone (context := sourceCtx) (elementType := elementType)) where
  targetType := Ty.optionType targetElementType
  targetRaw := RawTerm.optionNone
  targetTerm := Term.optionNone (context := targetCtx)
    (elementType := targetElementType)
  typeStrengthens := by
    change
      (match elementType.partialStrengthen? strengthening.back with
      | some strengthenedElementType =>
          some (Ty.optionType strengthenedElementType)
      | none => none) = some (Ty.optionType targetElementType)
    rw [elementTypeStrengthens]
  rawStrengthens := rfl
  typeRenames := by
    exact Ty.partialStrengthen?_imp_rename
      (Ty.optionType elementType)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.optionType targetElementType)
      (by
        change
          (match elementType.partialStrengthen? strengthening.back with
          | some strengthenedElementType =>
              some (Ty.optionType strengthenedElementType)
          | none => none) = some (Ty.optionType targetElementType)
        rw [elementTypeStrengthens])
  rawRenames := rfl

/-- Option-some strengthens by strengthening its payload. -/
def partialStrengthenTypedOptionSome {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueResult : StrengtheningResult strengthening valueTerm) :
    StrengtheningResult strengthening (Term.optionSome valueTerm) where
  targetType := Ty.optionType valueResult.targetType
  targetRaw := RawTerm.optionSome valueResult.targetRaw
  targetTerm := Term.optionSome valueResult.targetTerm
  typeStrengthens := by
    change
      (match elementType.partialStrengthen? strengthening.back with
      | some strengthenedElement =>
          some (Ty.optionType strengthenedElement)
      | none => none) =
        some (Ty.optionType valueResult.targetType)
    rw [valueResult.typeStrengthens]
  rawStrengthens := by
    change
      (match valueRaw.partialStrengthen? strengthening.back with
      | some strengthenedValue => some (RawTerm.optionSome strengthenedValue)
      | none => none) =
        some (RawTerm.optionSome valueResult.targetRaw)
    rw [valueResult.rawStrengthens]
  typeRenames := by
    simp only [Ty.rename]
    exact congrArg Ty.optionType valueResult.typeRenames
  rawRenames := by
    exact congrArg RawTerm.optionSome valueResult.rawRenames

/-- Modal introduction strengthens by strengthening its payload. -/
def partialStrengthenTypedModIntro {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerResult : StrengtheningResult strengthening innerTerm) :
    StrengtheningResult strengthening (Term.modIntro innerTerm) where
  targetType := innerResult.targetType
  targetRaw := RawTerm.modIntro innerResult.targetRaw
  targetTerm := Term.modIntro innerResult.targetTerm
  typeStrengthens := innerResult.typeStrengthens
  rawStrengthens := by
    change
      (match innerRaw.partialStrengthen? strengthening.back with
      | some strengthenedInner => some (RawTerm.modIntro strengthenedInner)
      | none => none) =
        some (RawTerm.modIntro innerResult.targetRaw)
    rw [innerResult.rawStrengthens]
  typeRenames := innerResult.typeRenames
  rawRenames := by
    exact congrArg RawTerm.modIntro innerResult.rawRenames

/-- Modal elimination strengthens by strengthening its payload. -/
def partialStrengthenTypedModElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerResult : StrengtheningResult strengthening innerTerm) :
    StrengtheningResult strengthening (Term.modElim innerTerm) where
  targetType := innerResult.targetType
  targetRaw := RawTerm.modElim innerResult.targetRaw
  targetTerm := Term.modElim innerResult.targetTerm
  typeStrengthens := innerResult.typeStrengthens
  rawStrengthens := by
    change
      (match innerRaw.partialStrengthen? strengthening.back with
      | some strengthenedInner => some (RawTerm.modElim strengthenedInner)
      | none => none) =
        some (RawTerm.modElim innerResult.targetRaw)
    rw [innerResult.rawStrengthens]
  typeRenames := innerResult.typeRenames
  rawRenames := by
    exact congrArg RawTerm.modElim innerResult.rawRenames

/-- Modal subsumption strengthens by strengthening its payload. -/
def partialStrengthenTypedSubsume {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerResult : StrengtheningResult strengthening innerTerm) :
    StrengtheningResult strengthening (Term.subsume innerTerm) where
  targetType := innerResult.targetType
  targetRaw := RawTerm.subsume innerResult.targetRaw
  targetTerm := Term.subsume innerResult.targetTerm
  typeStrengthens := innerResult.typeStrengthens
  rawStrengthens := by
    change
      (match innerRaw.partialStrengthen? strengthening.back with
      | some strengthenedInner => some (RawTerm.subsume strengthenedInner)
      | none => none) =
        some (RawTerm.subsume innerResult.targetRaw)
    rw [innerResult.rawStrengthens]
  typeRenames := innerResult.typeRenames
  rawRenames := by
    exact congrArg RawTerm.subsume innerResult.rawRenames

end Term

end LeanFX2
