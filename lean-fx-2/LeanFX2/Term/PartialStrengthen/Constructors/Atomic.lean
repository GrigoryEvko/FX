import LeanFX2.Term.PartialStrengthen.Core

/-! # Term/PartialStrengthen/Constructors/Atomic

Typed partial-strengthening producers for variables and atomic terms
whose recursive payload is absent.  Parametric atoms still require their
parameter type to strengthen, but they do not recurse on child terms.
-/

namespace LeanFX2

namespace Term

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

end Term

end LeanFX2
