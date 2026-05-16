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

/-- Natural successor strengthens by strengthening its predecessor. -/
def partialStrengthenTypedNatSucc {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {predecessorRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (predecessorResult :
      StrengtheningResult strengthening predecessor) :
    StrengtheningResult strengthening (Term.natSucc predecessor) := by
  cases predecessorResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      cases typeStrengthens
      exact {
        targetType := Ty.nat
        targetRaw := RawTerm.natSucc targetRaw
        targetTerm := Term.natSucc targetTerm
        typeStrengthens := rfl
        rawStrengthens := by
          change
            (match predecessorRaw.partialStrengthen? strengthening.back with
            | some strengthenedPredecessor =>
                some (RawTerm.natSucc strengthenedPredecessor)
            | none => none) =
              some (RawTerm.natSucc targetRaw)
          rw [rawStrengthens]
        typeRenames := rfl
        rawRenames := congrArg RawTerm.natSucc rawRenames
      }

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

/-- Interval negation strengthens by strengthening its payload. -/
def partialStrengthenTypedIntervalOpp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerResult : StrengtheningResult strengthening innerValue) :
    StrengtheningResult strengthening (Term.intervalOpp innerValue) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      cases typeStrengthens
      exact {
        targetType := Ty.interval
        targetRaw := RawTerm.intervalOpp targetRaw
        targetTerm := Term.intervalOpp targetTerm
        typeStrengthens := rfl
        rawStrengthens := by
          change
            (match innerRaw.partialStrengthen? strengthening.back with
            | some strengthenedInner => some (RawTerm.intervalOpp strengthenedInner)
            | none => none) =
              some (RawTerm.intervalOpp targetRaw)
          rw [rawStrengthens]
        typeRenames := rfl
        rawRenames := congrArg RawTerm.intervalOpp rawRenames
      }

/-- Interval meet strengthens by strengthening both operands. -/
def partialStrengthenTypedIntervalMeet {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftResult : StrengtheningResult strengthening leftValue)
    (rightResult : StrengtheningResult strengthening rightValue) :
    StrengtheningResult strengthening
      (Term.intervalMeet leftValue rightValue) := by
  cases leftResult with
  | mk leftTargetType leftTargetRaw leftTargetTerm leftTypeStrengthens
      leftRawStrengthens leftTypeRenames leftRawRenames =>
      cases rightResult with
      | mk rightTargetType rightTargetRaw rightTargetTerm rightTypeStrengthens
          rightRawStrengthens rightTypeRenames rightRawRenames =>
          cases leftTypeStrengthens
          cases rightTypeStrengthens
          exact {
            targetType := Ty.interval
            targetRaw := RawTerm.intervalMeet leftTargetRaw rightTargetRaw
            targetTerm := Term.intervalMeet leftTargetTerm rightTargetTerm
            typeStrengthens := rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (leftRaw.partialStrengthen? strengthening.back)
                  (rightRaw.partialStrengthen? strengthening.back)
                  RawTerm.intervalMeet =
                  some (RawTerm.intervalMeet leftTargetRaw rightTargetRaw)
              rw [leftRawStrengthens, rightRawStrengthens]
              rfl
            typeRenames := rfl
            rawRenames := by
              cases leftRawRenames
              cases rightRawRenames
              rfl
          }

/-- Interval join strengthens by strengthening both operands. -/
def partialStrengthenTypedIntervalJoin {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftResult : StrengtheningResult strengthening leftValue)
    (rightResult : StrengtheningResult strengthening rightValue) :
    StrengtheningResult strengthening
      (Term.intervalJoin leftValue rightValue) := by
  cases leftResult with
  | mk leftTargetType leftTargetRaw leftTargetTerm leftTypeStrengthens
      leftRawStrengthens leftTypeRenames leftRawRenames =>
      cases rightResult with
      | mk rightTargetType rightTargetRaw rightTargetTerm rightTypeStrengthens
          rightRawStrengthens rightTypeRenames rightRawRenames =>
          cases leftTypeStrengthens
          cases rightTypeStrengthens
          exact {
            targetType := Ty.interval
            targetRaw := RawTerm.intervalJoin leftTargetRaw rightTargetRaw
            targetTerm := Term.intervalJoin leftTargetTerm rightTargetTerm
            typeStrengthens := rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (leftRaw.partialStrengthen? strengthening.back)
                  (rightRaw.partialStrengthen? strengthening.back)
                  RawTerm.intervalJoin =
                  some (RawTerm.intervalJoin leftTargetRaw rightTargetRaw)
              rw [leftRawStrengthens, rightRawStrengthens]
              rfl
            typeRenames := rfl
            rawRenames := by
              cases leftRawRenames
              cases rightRawRenames
              rfl
          }

/-- Non-dependent function application strengthens by strengthening the
function and argument, then decomposing the strengthened arrow type. -/
def partialStrengthenTypedApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionResult : StrengtheningResult strengthening functionTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.app functionTerm argumentTerm) := by
  cases functionResult with
  | mk targetFunctionType targetFunctionRaw targetFunctionTerm
      functionTypeStrengthens functionRawStrengthens functionTypeRenames
      functionRawRenames =>
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back)
          Ty.arrow = some targetFunctionType at functionTypeStrengthens
      cases domainSuccess : domainType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [domainSuccess] at functionTypeStrengthens
          cases functionTypeStrengthens
      | some targetDomainType =>
          cases codomainSuccess : codomainType.partialStrengthen?
              strengthening.back with
          | none =>
              rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
              cases functionTypeStrengthens
          | some targetCodomainType =>
              rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
              cases functionTypeStrengthens
              cases argumentResult with
              | mk targetArgumentType targetArgumentRaw targetArgumentTerm
                  argumentTypeStrengthens argumentRawStrengthens
                  argumentTypeRenames argumentRawRenames =>
                  rw [domainSuccess] at argumentTypeStrengthens
                  cases argumentTypeStrengthens
                  exact {
                    targetType := targetCodomainType
                    targetRaw := RawTerm.app targetFunctionRaw targetArgumentRaw
                    targetTerm :=
                      Term.app targetFunctionTerm targetArgumentTerm
                    typeStrengthens := codomainSuccess
                    rawStrengthens := by
                      change
                        Option.mapTwo
                          (functionRaw.partialStrengthen? strengthening.back)
                          (argumentRaw.partialStrengthen? strengthening.back)
                          RawTerm.app =
                          some (RawTerm.app targetFunctionRaw
                            targetArgumentRaw)
                      rw [functionRawStrengthens, argumentRawStrengthens]
                      rfl
                    typeRenames :=
                      Ty.partialStrengthen?_imp_rename codomainType
                        strengthening.forward strengthening.back
                        strengthening.injectsBack targetCodomainType
                        codomainSuccess
                    rawRenames := by
                      cases functionRawRenames
                      cases argumentRawRenames
                      rfl
                  }

/-- Dependent function application strengthens by strengthening the
function, the argument, and the codomain under the lifted strengthening. -/
def partialStrengthenTypedAppPi {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionResult : StrengtheningResult strengthening functionTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.appPi functionTerm argumentTerm) := by
  cases functionResult with
  | mk targetFunctionType targetFunctionRaw targetFunctionTerm
      functionTypeStrengthens functionRawStrengthens functionTypeRenames
      functionRawRenames =>
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back.lift)
          Ty.piTy = some targetFunctionType at functionTypeStrengthens
      cases domainSuccess : domainType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [domainSuccess] at functionTypeStrengthens
          cases functionTypeStrengthens
      | some targetDomainType =>
          cases codomainSuccess : codomainType.partialStrengthen?
              strengthening.back.lift with
          | none =>
              rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
              cases functionTypeStrengthens
          | some targetCodomainType =>
              rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
              cases functionTypeStrengthens
              cases argumentResult with
              | mk targetArgumentType targetArgumentRaw targetArgumentTerm
                  argumentTypeStrengthens argumentRawStrengthens
                  argumentTypeRenames argumentRawRenames =>
                  rw [domainSuccess] at argumentTypeStrengthens
                  cases argumentTypeStrengthens
                  have resultTypeStrengthens :
                      (codomainType.subst0 domainType
                          argumentRaw).partialStrengthen?
                        strengthening.back =
                        some (targetCodomainType.subst0 targetDomainType
                          targetArgumentRaw) :=
                    Ty.partialStrengthen?_subst0_of_success codomainType
                      targetCodomainType domainType targetDomainType
                      argumentRaw targetArgumentRaw strengthening.forward
                      strengthening.back strengthening.injectsBack
                      strengthening.back_forward codomainSuccess
                      domainSuccess argumentRawStrengthens
                  exact {
                    targetType :=
                      targetCodomainType.subst0 targetDomainType
                        targetArgumentRaw
                    targetRaw :=
                      RawTerm.app targetFunctionRaw targetArgumentRaw
                    targetTerm :=
                      Term.appPi targetFunctionTerm targetArgumentTerm
                    typeStrengthens := resultTypeStrengthens
                    rawStrengthens := by
                      change
                        Option.mapTwo
                          (functionRaw.partialStrengthen? strengthening.back)
                          (argumentRaw.partialStrengthen? strengthening.back)
                          RawTerm.app =
                          some (RawTerm.app targetFunctionRaw
                            targetArgumentRaw)
                      rw [functionRawStrengthens, argumentRawStrengthens]
                      rfl
                    typeRenames :=
                      Ty.partialStrengthen?_imp_rename
                        (codomainType.subst0 domainType argumentRaw)
                        strengthening.forward strengthening.back
                        strengthening.injectsBack
                        (targetCodomainType.subst0 targetDomainType
                          targetArgumentRaw)
                        resultTypeStrengthens
                    rawRenames := by
                      cases functionRawRenames
                      cases argumentRawRenames
                      rfl
                  }

/-- Sigma pair strengthens by strengthening both components and the
binder-indexed second component type. -/
def partialStrengthenTypedPair {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {targetSecondType : Ty level (targetScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (secondTypeStrengthens :
      secondType.partialStrengthen? strengthening.back.lift =
        some targetSecondType)
    (firstResult : StrengtheningResult strengthening firstValue)
    (secondResult : StrengtheningResult strengthening secondValue) :
    StrengtheningResult strengthening
      (Term.pair firstValue secondValue) := by
  cases firstResult with
  | mk targetFirstType targetFirstRaw targetFirstTerm firstTypeStrengthens
      firstRawStrengthens firstTypeRenames firstRawRenames =>
      cases secondResult with
      | mk targetSecondValueType targetSecondRaw targetSecondTerm
          secondValueTypeStrengthens secondRawStrengthens
          secondValueTypeRenames secondRawRenames =>
          have expectedSecondValueStrengthens :
              (secondType.subst0 firstType firstRaw).partialStrengthen?
                  strengthening.back =
                some (targetSecondType.subst0 targetFirstType
                  targetFirstRaw) :=
            Ty.partialStrengthen?_subst0_of_success secondType
              targetSecondType firstType targetFirstType firstRaw
              targetFirstRaw strengthening.forward strengthening.back
              strengthening.injectsBack strengthening.back_forward
              secondTypeStrengthens firstTypeStrengthens
              firstRawStrengthens
          rw [expectedSecondValueStrengthens] at secondValueTypeStrengthens
          cases secondValueTypeStrengthens
          exact {
            targetType := Ty.sigmaTy targetFirstType targetSecondType
            targetRaw := RawTerm.pair targetFirstRaw targetSecondRaw
            targetTerm := Term.pair targetFirstTerm targetSecondTerm
            typeStrengthens := by
              change
                Option.mapTwo
                  (firstType.partialStrengthen? strengthening.back)
                  (secondType.partialStrengthen? strengthening.back.lift)
                  Ty.sigmaTy =
                  some (Ty.sigmaTy targetFirstType targetSecondType)
              rw [firstTypeStrengthens, secondTypeStrengthens]
              rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (firstRaw.partialStrengthen? strengthening.back)
                  (secondRaw.partialStrengthen? strengthening.back)
                  RawTerm.pair =
                  some (RawTerm.pair targetFirstRaw targetSecondRaw)
              rw [firstRawStrengthens, secondRawStrengthens]
              rfl
            typeRenames := by
              simp only [Ty.rename]
              rw [firstTypeRenames]
              exact congrArg (Ty.sigmaTy (targetFirstType.rename
                  strengthening.forward))
                (Ty.partialStrengthen?_imp_rename secondType
                  strengthening.forward.lift strengthening.back.lift
                  (PartialRawRenaming.lift_renamingInjectsBack
                    strengthening.injectsBack)
                  targetSecondType secondTypeStrengthens)
            rawRenames := by
              cases firstRawRenames
              cases secondRawRenames
              rfl
          }

/-- Sigma first projection strengthens by strengthening its pair payload. -/
def partialStrengthenTypedFst {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairResult : StrengtheningResult strengthening pairTerm) :
    StrengtheningResult strengthening (Term.fst pairTerm) := by
  cases pairResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      change
        Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = some targetType at typeStrengthens
      cases firstSuccess : firstType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [firstSuccess] at typeStrengthens
          cases typeStrengthens
      | some targetFirstType =>
          cases secondSuccess : secondType.partialStrengthen?
              strengthening.back.lift with
          | none =>
              rw [firstSuccess, secondSuccess] at typeStrengthens
              cases typeStrengthens
          | some targetSecondType =>
              rw [firstSuccess, secondSuccess] at typeStrengthens
              cases typeStrengthens
              exact {
                targetType := targetFirstType
                targetRaw := RawTerm.fst targetRaw
                targetTerm := Term.fst targetTerm
                typeStrengthens := firstSuccess
                rawStrengthens := by
                  change
                    (match pairRaw.partialStrengthen? strengthening.back with
                    | some strengthenedPair => some (RawTerm.fst strengthenedPair)
                    | none => none) =
                      some (RawTerm.fst targetRaw)
                  rw [rawStrengthens]
                typeRenames := by
                  injection typeRenames
                rawRenames := congrArg RawTerm.fst rawRenames
              }

/-- Sigma second projection strengthens by strengthening its pair payload
and rebuilding the dependent result type with the strengthened first
projection. -/
def partialStrengthenTypedSnd {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairResult : StrengtheningResult strengthening pairTerm) :
    StrengtheningResult strengthening (Term.snd pairTerm) := by
  cases pairResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      change
        Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = some targetType at typeStrengthens
      cases firstSuccess : firstType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [firstSuccess] at typeStrengthens
          cases typeStrengthens
      | some targetFirstType =>
          cases secondSuccess : secondType.partialStrengthen?
              strengthening.back.lift with
          | none =>
              rw [firstSuccess, secondSuccess] at typeStrengthens
              cases typeStrengthens
          | some targetSecondType =>
              rw [firstSuccess, secondSuccess] at typeStrengthens
              cases typeStrengthens
              have fstRawStrengthens :
                  (RawTerm.fst pairRaw).partialStrengthen?
                      strengthening.back =
                    some (RawTerm.fst targetRaw) := by
                change
                  (match pairRaw.partialStrengthen? strengthening.back with
                  | some strengthenedPair => some (RawTerm.fst strengthenedPair)
                  | none => none) =
                    some (RawTerm.fst targetRaw)
                rw [rawStrengthens]
              have sndTypeStrengthens :
                  (secondType.subst0 firstType
                      (RawTerm.fst pairRaw)).partialStrengthen?
                    strengthening.back =
                    some (targetSecondType.subst0 targetFirstType
                      (RawTerm.fst targetRaw)) :=
                Ty.partialStrengthen?_subst0_of_success secondType
                  targetSecondType firstType targetFirstType
                  (RawTerm.fst pairRaw) (RawTerm.fst targetRaw)
                  strengthening.forward strengthening.back
                  strengthening.injectsBack strengthening.back_forward
                  secondSuccess firstSuccess fstRawStrengthens
              exact {
                targetType := targetSecondType.subst0 targetFirstType
                  (RawTerm.fst targetRaw)
                targetRaw := RawTerm.snd targetRaw
                targetTerm := Term.snd targetTerm
                typeStrengthens := sndTypeStrengthens
                rawStrengthens := by
                  change
                    (match pairRaw.partialStrengthen? strengthening.back with
                    | some strengthenedPair => some (RawTerm.snd strengthenedPair)
                    | none => none) =
                      some (RawTerm.snd targetRaw)
                  rw [rawStrengthens]
                typeRenames :=
                  Ty.partialStrengthen?_imp_rename
                    (secondType.subst0 firstType (RawTerm.fst pairRaw))
                    strengthening.forward strengthening.back
                    strengthening.injectsBack
                    (targetSecondType.subst0 targetFirstType
                      (RawTerm.fst targetRaw))
                    sndTypeStrengthens
                rawRenames := congrArg RawTerm.snd rawRenames
              }

/-- Record introduction strengthens by strengthening its field. -/
def partialStrengthenTypedRecordIntro {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (fieldResult : StrengtheningResult strengthening firstField) :
    StrengtheningResult strengthening (Term.recordIntro firstField) where
  targetType := Ty.record fieldResult.targetType
  targetRaw := RawTerm.recordIntro fieldResult.targetRaw
  targetTerm := Term.recordIntro fieldResult.targetTerm
  typeStrengthens := by
    change
      (match singleFieldType.partialStrengthen? strengthening.back with
      | some strengthenedField => some (Ty.record strengthenedField)
      | none => none) =
        some (Ty.record fieldResult.targetType)
    rw [fieldResult.typeStrengthens]
  rawStrengthens := by
    change
      (match firstRaw.partialStrengthen? strengthening.back with
      | some strengthenedField => some (RawTerm.recordIntro strengthenedField)
      | none => none) =
        some (RawTerm.recordIntro fieldResult.targetRaw)
    rw [fieldResult.rawStrengthens]
  typeRenames := congrArg Ty.record fieldResult.typeRenames
  rawRenames := congrArg RawTerm.recordIntro fieldResult.rawRenames

/-- Record projection strengthens by strengthening its record payload. -/
def partialStrengthenTypedRecordProj {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (recordResult : StrengtheningResult strengthening recordValue) :
    StrengtheningResult strengthening (Term.recordProj recordValue) := by
  cases recordResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      change
        (match singleFieldType.partialStrengthen? strengthening.back with
        | some strengthenedField => some (Ty.record strengthenedField)
        | none => none) = some targetType at typeStrengthens
      cases fieldSuccess : singleFieldType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [fieldSuccess] at typeStrengthens
          cases typeStrengthens
      | some targetFieldType =>
          rw [fieldSuccess] at typeStrengthens
          cases typeStrengthens
          exact {
            targetType := targetFieldType
            targetRaw := RawTerm.recordProj targetRaw
            targetTerm := Term.recordProj targetTerm
            typeStrengthens := fieldSuccess
            rawStrengthens := by
              change
                (match recordRaw.partialStrengthen? strengthening.back with
                | some strengthenedRecord =>
                    some (RawTerm.recordProj strengthenedRecord)
                | none => none) =
                  some (RawTerm.recordProj targetRaw)
              rw [rawStrengthens]
            typeRenames := by
              injection typeRenames
            rawRenames := congrArg RawTerm.recordProj rawRenames
          }

end Term

end LeanFX2
