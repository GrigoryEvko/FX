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

/-- Natural-number eliminator strengthens by strengthening the scrutinee,
zero branch, and successor branch, then aligning the shared motive type
through the zero branch. -/
def partialStrengthenTypedNatElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (zeroResult : StrengtheningResult strengthening zeroBranch)
    (succResult : StrengtheningResult strengthening succBranch) :
    StrengtheningResult strengthening
      (Term.natElim scrutinee zeroBranch succBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      cases scrutineeTypeStrengthens
      cases zeroResult with
      | mk targetMotiveType targetZeroRaw targetZeroTerm
          zeroTypeStrengthens zeroRawStrengthens zeroTypeRenames
          zeroRawRenames =>
          cases succResult with
          | mk targetSuccType targetSuccRaw targetSuccTerm
              succTypeStrengthens succRawStrengthens succTypeRenames
              succRawRenames =>
              change
                Option.mapTwo
                  (Ty.nat.partialStrengthen? strengthening.back)
                  (motiveType.partialStrengthen? strengthening.back)
                  Ty.arrow = some targetSuccType at succTypeStrengthens
              rw [zeroTypeStrengthens] at succTypeStrengthens
              cases succTypeStrengthens
              exact {
                targetType := targetMotiveType
                targetRaw := RawTerm.natElim targetScrutineeRaw
                  targetZeroRaw targetSuccRaw
                targetTerm := Term.natElim targetScrutineeTerm
                  targetZeroTerm targetSuccTerm
                typeStrengthens := zeroTypeStrengthens
                rawStrengthens := by
                  change
                    Option.mapThree
                      (scrutineeRaw.partialStrengthen? strengthening.back)
                      (zeroRaw.partialStrengthen? strengthening.back)
                      (succRaw.partialStrengthen? strengthening.back)
                      RawTerm.natElim =
                        some (RawTerm.natElim targetScrutineeRaw
                          targetZeroRaw targetSuccRaw)
                  rw [scrutineeRawStrengthens, zeroRawStrengthens,
                    succRawStrengthens]
                  rfl
                typeRenames := zeroTypeRenames
                rawRenames := by
                  cases scrutineeRawRenames
                  cases zeroRawRenames
                  cases succRawRenames
                  rfl
              }

/-- Natural-number recursor strengthens by strengthening the scrutinee,
zero branch, and binary successor branch, then aligning the nested arrow
type through the zero branch's strengthened motive. -/
def partialStrengthenTypedNatRec {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (zeroResult : StrengtheningResult strengthening zeroBranch)
    (succResult : StrengtheningResult strengthening succBranch) :
    StrengtheningResult strengthening
      (Term.natRec scrutinee zeroBranch succBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      cases scrutineeTypeStrengthens
      cases zeroResult with
      | mk targetMotiveType targetZeroRaw targetZeroTerm
          zeroTypeStrengthens zeroRawStrengthens zeroTypeRenames
          zeroRawRenames =>
          cases succResult with
          | mk targetSuccType targetSuccRaw targetSuccTerm
              succTypeStrengthens succRawStrengthens succTypeRenames
              succRawRenames =>
              change
                Option.mapTwo
                  (Ty.nat.partialStrengthen? strengthening.back)
                  (Option.mapTwo
                    (motiveType.partialStrengthen? strengthening.back)
                    (motiveType.partialStrengthen? strengthening.back)
                    Ty.arrow)
                  Ty.arrow = some targetSuccType at succTypeStrengthens
              rw [zeroTypeStrengthens] at succTypeStrengthens
              cases succTypeStrengthens
              exact {
                targetType := targetMotiveType
                targetRaw := RawTerm.natRec targetScrutineeRaw
                  targetZeroRaw targetSuccRaw
                targetTerm := Term.natRec targetScrutineeTerm
                  targetZeroTerm targetSuccTerm
                typeStrengthens := zeroTypeStrengthens
                rawStrengthens := by
                  change
                    Option.mapThree
                      (scrutineeRaw.partialStrengthen? strengthening.back)
                      (zeroRaw.partialStrengthen? strengthening.back)
                      (succRaw.partialStrengthen? strengthening.back)
                      RawTerm.natRec =
                        some (RawTerm.natRec targetScrutineeRaw
                          targetZeroRaw targetSuccRaw)
                  rw [scrutineeRawStrengthens, zeroRawStrengthens,
                    succRawStrengthens]
                  rfl
                typeRenames := zeroTypeRenames
                rawRenames := by
                  cases scrutineeRawRenames
                  cases zeroRawRenames
                  cases succRawRenames
                  rfl
              }

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

/-- Non-dependent lambda strengthens by strengthening its domain and
codomain types, then strengthening the body under the lifted context
strengthening. -/
def partialStrengthenTypedLam {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainTypeStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (bodyResult : StrengtheningResult
      (strengthening.lift domainType targetDomainType
        domainTypeStrengthens) body) :
    StrengtheningResult strengthening (Term.lam body) := by
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have bodyRawStrengthensAtLift :
          bodyRaw.partialStrengthen? strengthening.back.lift =
            some targetBodyRaw := by
        simpa only [ContextStrengthening.lift] using bodyRawStrengthens
      have expectedBodyTypeStrengthens :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift codomainType
          strengthening.back, codomainTypeStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      exact {
        targetType := Ty.arrow targetDomainType targetCodomainType
        targetRaw := RawTerm.lam targetBodyRaw
        targetTerm := Term.lam targetBodyTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (domainType.partialStrengthen? strengthening.back)
              (codomainType.partialStrengthen? strengthening.back)
              Ty.arrow =
              some (Ty.arrow targetDomainType targetCodomainType)
          rw [domainTypeStrengthens, codomainTypeStrengthens]
          rfl
        rawStrengthens := by
          change
            (match bodyRaw.partialStrengthen? strengthening.back.lift with
            | some strengthenedBody => some (RawTerm.lam strengthenedBody)
            | none => none) =
              some (RawTerm.lam targetBodyRaw)
          rw [bodyRawStrengthensAtLift]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.arrow domainType codomainType)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.arrow targetDomainType targetCodomainType)
            (by
              change
                Option.mapTwo
                  (domainType.partialStrengthen? strengthening.back)
                  (codomainType.partialStrengthen? strengthening.back)
                  Ty.arrow =
                  some (Ty.arrow targetDomainType targetCodomainType)
              rw [domainTypeStrengthens, codomainTypeStrengthens]
              rfl)
        rawRenames :=
          RawTerm.partialStrengthen?_imp_rename
            (RawTerm.lam bodyRaw) strengthening.forward strengthening.back
            strengthening.injectsBack (RawTerm.lam targetBodyRaw)
            (by
              change
                (match bodyRaw.partialStrengthen?
                    strengthening.back.lift with
                | some strengthenedBody => some (RawTerm.lam strengthenedBody)
                | none => none) =
                  some (RawTerm.lam targetBodyRaw)
              rw [bodyRawStrengthensAtLift])
      }

/-- Dependent lambda strengthens by strengthening its domain type and
body under the lifted context strengthening. -/
def partialStrengthenTypedLamPi {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (bodyResult : StrengtheningResult
      (strengthening.lift domainType targetDomainType
        domainTypeStrengthens) body) :
    StrengtheningResult strengthening (Term.lamPi body) := by
  cases bodyResult with
  | mk targetCodomainType targetBodyRaw targetBodyTerm
      codomainTypeStrengthens bodyRawStrengthens codomainTypeRenames
      bodyRawRenames =>
      have codomainTypeStrengthensAtLift :
          codomainType.partialStrengthen? strengthening.back.lift =
            some targetCodomainType := by
        simpa only [ContextStrengthening.lift] using codomainTypeStrengthens
      have bodyRawStrengthensAtLift :
          bodyRaw.partialStrengthen? strengthening.back.lift =
            some targetBodyRaw := by
        simpa only [ContextStrengthening.lift] using bodyRawStrengthens
      exact {
        targetType := Ty.piTy targetDomainType targetCodomainType
        targetRaw := RawTerm.lam targetBodyRaw
        targetTerm := Term.lamPi targetBodyTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (domainType.partialStrengthen? strengthening.back)
              (codomainType.partialStrengthen? strengthening.back.lift)
              Ty.piTy =
              some (Ty.piTy targetDomainType targetCodomainType)
          rw [domainTypeStrengthens, codomainTypeStrengthensAtLift]
          rfl
        rawStrengthens := by
          change
            (match bodyRaw.partialStrengthen? strengthening.back.lift with
            | some strengthenedBody => some (RawTerm.lam strengthenedBody)
            | none => none) =
              some (RawTerm.lam targetBodyRaw)
          rw [bodyRawStrengthensAtLift]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.piTy domainType codomainType)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.piTy targetDomainType targetCodomainType)
            (by
              change
                Option.mapTwo
                  (domainType.partialStrengthen? strengthening.back)
                  (codomainType.partialStrengthen? strengthening.back.lift)
                  Ty.piTy =
                  some (Ty.piTy targetDomainType targetCodomainType)
              rw [domainTypeStrengthens, codomainTypeStrengthensAtLift]
              rfl)
        rawRenames :=
          RawTerm.partialStrengthen?_imp_rename
            (RawTerm.lam bodyRaw) strengthening.forward strengthening.back
            strengthening.injectsBack (RawTerm.lam targetBodyRaw)
            (by
              change
                (match bodyRaw.partialStrengthen?
                    strengthening.back.lift with
                | some strengthenedBody => some (RawTerm.lam strengthenedBody)
                | none => none) =
                  some (RawTerm.lam targetBodyRaw)
              rw [bodyRawStrengthensAtLift])
      }

/-- Cubical path lambda strengthens by strengthening the carrier and
endpoints, then strengthening the body under the lifted interval
context. -/
def partialStrengthenTypedPathLam {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (carrierStrengthens :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftEndpointStrengthens :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightEndpointStrengthens :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (bodyResult : StrengtheningResult
      (strengthening.lift Ty.interval Ty.interval rfl) body) :
    StrengtheningResult strengthening
      (Term.pathLam modeIsUnivalent carrierType leftEndpoint
        rightEndpoint body) := by
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          carrierType.weaken.partialStrengthen? strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have bodyRawStrengthensAtLift :
          bodyRaw.partialStrengthen? strengthening.back.lift =
            some targetBodyRaw := by
        simpa only [ContextStrengthening.lift] using bodyRawStrengthens
      have expectedBodyTypeStrengthens :
          carrierType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCarrierType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift carrierType
          strengthening.back, carrierStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      exact {
        targetType :=
          Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint
        targetRaw := RawTerm.pathLam targetBodyRaw
        targetTerm := Term.pathLam modeIsUnivalent targetCarrierType
          targetLeftEndpoint targetRightEndpoint targetBodyTerm
        typeStrengthens := by
          change
            Option.mapThree
              (carrierType.partialStrengthen? strengthening.back)
              (leftEndpoint.partialStrengthen? strengthening.back)
              (rightEndpoint.partialStrengthen? strengthening.back)
              Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
          rw [carrierStrengthens, leftEndpointStrengthens,
            rightEndpointStrengthens]
          rfl
        rawStrengthens := by
          change
            (match bodyRaw.partialStrengthen? strengthening.back.lift with
            | some strengthenedBody => some (RawTerm.pathLam strengthenedBody)
            | none => none) =
              some (RawTerm.pathLam targetBodyRaw)
          rw [bodyRawStrengthensAtLift]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.path carrierType leftEndpoint rightEndpoint)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint)
            (by
              change
                Option.mapThree
                  (carrierType.partialStrengthen? strengthening.back)
                  (leftEndpoint.partialStrengthen? strengthening.back)
                  (rightEndpoint.partialStrengthen? strengthening.back)
                  Ty.path =
                  some (Ty.path targetCarrierType targetLeftEndpoint
                    targetRightEndpoint)
              rw [carrierStrengthens, leftEndpointStrengthens,
                rightEndpointStrengthens]
              rfl)
        rawRenames :=
          RawTerm.partialStrengthen?_imp_rename
            (RawTerm.pathLam bodyRaw) strengthening.forward
            strengthening.back strengthening.injectsBack
            (RawTerm.pathLam targetBodyRaw)
            (by
              change
                (match bodyRaw.partialStrengthen?
                    strengthening.back.lift with
                | some strengthenedBody =>
                    some (RawTerm.pathLam strengthenedBody)
                | none => none) =
                  some (RawTerm.pathLam targetBodyRaw)
              rw [bodyRawStrengthensAtLift])
      }

/-- Cubical path application strengthens by strengthening the path and
interval argument. -/
def partialStrengthenTypedPathApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathResult : StrengtheningResult strengthening pathTerm)
    (intervalResult : StrengtheningResult strengthening intervalTerm) :
    StrengtheningResult strengthening
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPathTerm pathTypeStrengthens
      pathRawStrengthens pathTypeRenames pathRawRenames =>
      change
        Option.mapThree
          (carrierType.partialStrengthen? strengthening.back)
          (leftEndpoint.partialStrengthen? strengthening.back)
          (rightEndpoint.partialStrengthen? strengthening.back)
          Ty.path = some targetPathType at pathTypeStrengthens
      cases carrierSuccess : carrierType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [carrierSuccess] at pathTypeStrengthens
          cases pathTypeStrengthens
      | some targetCarrierType =>
          cases leftSuccess : leftEndpoint.partialStrengthen?
              strengthening.back with
          | none =>
              rw [carrierSuccess, leftSuccess] at pathTypeStrengthens
              cases pathTypeStrengthens
          | some targetLeftEndpoint =>
              cases rightSuccess : rightEndpoint.partialStrengthen?
                  strengthening.back with
              | none =>
                  rw [carrierSuccess, leftSuccess, rightSuccess] at pathTypeStrengthens
                  cases pathTypeStrengthens
              | some targetRightEndpoint =>
                  rw [carrierSuccess, leftSuccess, rightSuccess] at pathTypeStrengthens
                  cases pathTypeStrengthens
                  cases intervalResult with
                  | mk targetIntervalType targetIntervalRaw targetIntervalTerm
                      intervalTypeStrengthens intervalRawStrengthens
                      intervalTypeRenames intervalRawRenames =>
                      cases intervalTypeStrengthens
                      exact {
                        targetType := targetCarrierType
                        targetRaw :=
                          RawTerm.pathApp targetPathRaw targetIntervalRaw
                        targetTerm := Term.pathApp modeIsUnivalent
                          targetPathTerm targetIntervalTerm
                        typeStrengthens := carrierSuccess
                        rawStrengthens := by
                          change
                            Option.mapTwo
                              (pathRaw.partialStrengthen?
                                strengthening.back)
                              (intervalRaw.partialStrengthen?
                                strengthening.back)
                              RawTerm.pathApp =
                              some (RawTerm.pathApp targetPathRaw
                                targetIntervalRaw)
                          rw [pathRawStrengthens, intervalRawStrengthens]
                          rfl
                        typeRenames :=
                          Ty.partialStrengthen?_imp_rename carrierType
                            strengthening.forward strengthening.back
                            strengthening.injectsBack targetCarrierType
                            carrierSuccess
                        rawRenames := by
                          cases pathRawRenames
                          cases intervalRawRenames
                          rfl
                      }

/-- List cons strengthens by strengthening the head and tail, then
aligning the shared element type through the tail's list type. -/
def partialStrengthenTypedListCons {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headResult : StrengtheningResult strengthening headTerm)
    (tailResult : StrengtheningResult strengthening tailTerm) :
    StrengtheningResult strengthening
      (Term.listCons headTerm tailTerm) := by
  cases headResult with
  | mk targetElementType targetHeadRaw targetHeadTerm headTypeStrengthens
      headRawStrengthens headTypeRenames headRawRenames =>
      cases tailResult with
      | mk targetTailType targetTailRaw targetTailTerm tailTypeStrengthens
          tailRawStrengthens tailTypeRenames tailRawRenames =>
          change
            (match elementType.partialStrengthen? strengthening.back with
            | some strengthenedElement => some (Ty.listType strengthenedElement)
            | none => none) = some targetTailType at tailTypeStrengthens
          rw [headTypeStrengthens] at tailTypeStrengthens
          cases tailTypeStrengthens
          exact {
            targetType := Ty.listType targetElementType
            targetRaw := RawTerm.listCons targetHeadRaw targetTailRaw
            targetTerm := Term.listCons targetHeadTerm targetTailTerm
            typeStrengthens := by
              change
                (match elementType.partialStrengthen? strengthening.back with
                | some strengthenedElement =>
                    some (Ty.listType strengthenedElement)
                | none => none) =
                  some (Ty.listType targetElementType)
              rw [headTypeStrengthens]
            rawStrengthens := by
              change
                Option.mapTwo
                  (headRaw.partialStrengthen? strengthening.back)
                  (tailRaw.partialStrengthen? strengthening.back)
                  RawTerm.listCons =
                  some (RawTerm.listCons targetHeadRaw targetTailRaw)
              rw [headRawStrengthens, tailRawStrengthens]
              rfl
            typeRenames := congrArg Ty.listType headTypeRenames
            rawRenames := by
              cases headRawRenames
              cases tailRawRenames
              rfl
          }

/-- List eliminator strengthens by strengthening the scrutinee, nil
branch, and cons branch, then aligning the element and motive indices
through the scrutinee and nil branch. -/
def partialStrengthenTypedListElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (nilResult : StrengtheningResult strengthening nilBranch)
    (consResult : StrengtheningResult strengthening consBranch) :
    StrengtheningResult strengthening
      (Term.listElim scrutinee nilBranch consBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      change
        (match elementType.partialStrengthen? strengthening.back with
        | some strengthenedElement => some (Ty.listType strengthenedElement)
        | none => none) = some targetScrutineeType at scrutineeTypeStrengthens
      cases elementSuccess : elementType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [elementSuccess] at scrutineeTypeStrengthens
          cases scrutineeTypeStrengthens
      | some targetElementType =>
          rw [elementSuccess] at scrutineeTypeStrengthens
          cases scrutineeTypeStrengthens
          cases nilResult with
          | mk targetMotiveType targetNilRaw targetNilTerm
              nilTypeStrengthens nilRawStrengthens nilTypeRenames
              nilRawRenames =>
              cases consResult with
              | mk targetConsType targetConsRaw targetConsTerm
                  consTypeStrengthens consRawStrengthens consTypeRenames
                  consRawRenames =>
                  change
                    Option.mapTwo
                      (elementType.partialStrengthen? strengthening.back)
                      (Option.mapTwo
                        (match elementType.partialStrengthen?
                            strengthening.back with
                        | some strengthenedElement =>
                            some (Ty.listType strengthenedElement)
                        | none => none)
                        (motiveType.partialStrengthen? strengthening.back)
                        Ty.arrow)
                      Ty.arrow = some targetConsType at consTypeStrengthens
                  rw [elementSuccess, nilTypeStrengthens] at consTypeStrengthens
                  cases consTypeStrengthens
                  exact {
                    targetType := targetMotiveType
                    targetRaw := RawTerm.listElim targetScrutineeRaw
                      targetNilRaw targetConsRaw
                    targetTerm := Term.listElim targetScrutineeTerm
                      targetNilTerm targetConsTerm
                    typeStrengthens := nilTypeStrengthens
                    rawStrengthens := by
                      change
                        Option.mapThree
                          (scrutineeRaw.partialStrengthen?
                            strengthening.back)
                          (nilRaw.partialStrengthen? strengthening.back)
                          (consRaw.partialStrengthen? strengthening.back)
                          RawTerm.listElim =
                            some (RawTerm.listElim targetScrutineeRaw
                              targetNilRaw targetConsRaw)
                      rw [scrutineeRawStrengthens, nilRawStrengthens,
                        consRawStrengthens]
                      rfl
                    typeRenames := nilTypeRenames
                    rawRenames := by
                      cases scrutineeRawRenames
                      cases nilRawRenames
                      cases consRawRenames
                      rfl
                  }

/-- Either-left injection strengthens by strengthening the payload and
the unused right type index. -/
def partialStrengthenTypedEitherInlOfRightType {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    {targetRightType : Ty level targetScope}
    {valueRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (rightTypeStrengthens :
      rightType.partialStrengthen? strengthening.back =
        some targetRightType)
    (valueResult : StrengtheningResult strengthening valueTerm) :
    StrengtheningResult strengthening (Term.eitherInl
      (rightType := rightType) valueTerm) where
  targetType := Ty.eitherType valueResult.targetType targetRightType
  targetRaw := RawTerm.eitherInl valueResult.targetRaw
  targetTerm := Term.eitherInl (rightType := targetRightType)
    valueResult.targetTerm
  typeStrengthens := by
    change
      Option.mapTwo
        (leftType.partialStrengthen? strengthening.back)
        (rightType.partialStrengthen? strengthening.back)
        Ty.eitherType =
        some (Ty.eitherType valueResult.targetType targetRightType)
    rw [valueResult.typeStrengthens, rightTypeStrengthens]
    rfl
  rawStrengthens := by
    change
      (match valueRaw.partialStrengthen? strengthening.back with
      | some strengthenedValue => some (RawTerm.eitherInl strengthenedValue)
      | none => none) =
        some (RawTerm.eitherInl valueResult.targetRaw)
    rw [valueResult.rawStrengthens]
  typeRenames := by
    exact Ty.partialStrengthen?_imp_rename
      (Ty.eitherType leftType rightType)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.eitherType valueResult.targetType targetRightType)
      (by
        change
          Option.mapTwo
            (leftType.partialStrengthen? strengthening.back)
            (rightType.partialStrengthen? strengthening.back)
            Ty.eitherType =
            some (Ty.eitherType valueResult.targetType targetRightType)
        rw [valueResult.typeStrengthens, rightTypeStrengthens]
        rfl)
  rawRenames := congrArg RawTerm.eitherInl valueResult.rawRenames

/-- Either-right injection strengthens by strengthening the payload and
the unused left type index. -/
def partialStrengthenTypedEitherInrOfLeftType {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    {targetLeftType : Ty level targetScope}
    {valueRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (leftTypeStrengthens :
      leftType.partialStrengthen? strengthening.back =
        some targetLeftType)
    (valueResult : StrengtheningResult strengthening valueTerm) :
    StrengtheningResult strengthening (Term.eitherInr
      (leftType := leftType) valueTerm) where
  targetType := Ty.eitherType targetLeftType valueResult.targetType
  targetRaw := RawTerm.eitherInr valueResult.targetRaw
  targetTerm := Term.eitherInr (leftType := targetLeftType)
    valueResult.targetTerm
  typeStrengthens := by
    change
      Option.mapTwo
        (leftType.partialStrengthen? strengthening.back)
        (rightType.partialStrengthen? strengthening.back)
        Ty.eitherType =
        some (Ty.eitherType targetLeftType valueResult.targetType)
    rw [leftTypeStrengthens, valueResult.typeStrengthens]
    rfl
  rawStrengthens := by
    change
      (match valueRaw.partialStrengthen? strengthening.back with
      | some strengthenedValue => some (RawTerm.eitherInr strengthenedValue)
      | none => none) =
        some (RawTerm.eitherInr valueResult.targetRaw)
    rw [valueResult.rawStrengthens]
  typeRenames := by
    exact Ty.partialStrengthen?_imp_rename
      (Ty.eitherType leftType rightType)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.eitherType targetLeftType valueResult.targetType)
      (by
        change
          Option.mapTwo
            (leftType.partialStrengthen? strengthening.back)
            (rightType.partialStrengthen? strengthening.back)
            Ty.eitherType =
            some (Ty.eitherType targetLeftType valueResult.targetType)
        rw [leftTypeStrengthens, valueResult.typeStrengthens]
        rfl)
  rawRenames := congrArg RawTerm.eitherInr valueResult.rawRenames

/-- Option match strengthens by strengthening the scrutinee, none
branch, and some branch, then aligning the element and motive indices
through the scrutinee and none branch. -/
def partialStrengthenTypedOptionMatch {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (noneResult : StrengtheningResult strengthening noneBranch)
    (someResult : StrengtheningResult strengthening someBranch) :
    StrengtheningResult strengthening
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      change
        (match elementType.partialStrengthen? strengthening.back with
        | some strengthenedElement =>
            some (Ty.optionType strengthenedElement)
        | none => none) = some targetScrutineeType at scrutineeTypeStrengthens
      cases elementSuccess : elementType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [elementSuccess] at scrutineeTypeStrengthens
          cases scrutineeTypeStrengthens
      | some targetElementType =>
          rw [elementSuccess] at scrutineeTypeStrengthens
          cases scrutineeTypeStrengthens
          cases noneResult with
          | mk targetMotiveType targetNoneRaw targetNoneTerm
              noneTypeStrengthens noneRawStrengthens noneTypeRenames
              noneRawRenames =>
              cases someResult with
              | mk targetSomeType targetSomeRaw targetSomeTerm
                  someTypeStrengthens someRawStrengthens someTypeRenames
                  someRawRenames =>
                  change
                    Option.mapTwo
                      (elementType.partialStrengthen? strengthening.back)
                      (motiveType.partialStrengthen? strengthening.back)
                      Ty.arrow = some targetSomeType at someTypeStrengthens
                  rw [elementSuccess, noneTypeStrengthens] at someTypeStrengthens
                  cases someTypeStrengthens
                  exact {
                    targetType := targetMotiveType
                    targetRaw := RawTerm.optionMatch targetScrutineeRaw
                      targetNoneRaw targetSomeRaw
                    targetTerm := Term.optionMatch targetScrutineeTerm
                      targetNoneTerm targetSomeTerm
                    typeStrengthens := noneTypeStrengthens
                    rawStrengthens := by
                      change
                        Option.mapThree
                          (scrutineeRaw.partialStrengthen?
                            strengthening.back)
                          (noneRaw.partialStrengthen? strengthening.back)
                          (someRaw.partialStrengthen? strengthening.back)
                          RawTerm.optionMatch =
                            some (RawTerm.optionMatch targetScrutineeRaw
                              targetNoneRaw targetSomeRaw)
                      rw [scrutineeRawStrengthens, noneRawStrengthens,
                        someRawStrengthens]
                      rfl
                    typeRenames := noneTypeRenames
                    rawRenames := by
                      cases scrutineeRawRenames
                      cases noneRawRenames
                      cases someRawRenames
                      rfl
                  }

/-- Either match strengthens by strengthening the scrutinee and both
branches, then aligning the left, right, and motive indices through the
scrutinee and branch result types. -/
def partialStrengthenTypedEitherMatch {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (leftResult : StrengtheningResult strengthening leftBranch)
    (rightResult : StrengtheningResult strengthening rightBranch) :
    StrengtheningResult strengthening
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      change
        Option.mapTwo
          (leftType.partialStrengthen? strengthening.back)
          (rightType.partialStrengthen? strengthening.back)
          Ty.eitherType = some targetScrutineeType at scrutineeTypeStrengthens
      cases leftSuccess : leftType.partialStrengthen? strengthening.back with
      | none =>
          rw [leftSuccess] at scrutineeTypeStrengthens
          cases scrutineeTypeStrengthens
      | some targetLeftType =>
          cases rightSuccess : rightType.partialStrengthen?
              strengthening.back with
          | none =>
              rw [leftSuccess, rightSuccess] at scrutineeTypeStrengthens
              cases scrutineeTypeStrengthens
          | some targetRightType =>
              rw [leftSuccess, rightSuccess] at scrutineeTypeStrengthens
              cases scrutineeTypeStrengthens
              cases leftResult with
              | mk targetLeftBranchType targetLeftRaw targetLeftTerm
                  leftTypeStrengthens leftRawStrengthens leftTypeRenames
                  leftRawRenames =>
                  change
                    Option.mapTwo
                      (leftType.partialStrengthen? strengthening.back)
                      (motiveType.partialStrengthen? strengthening.back)
                      Ty.arrow = some targetLeftBranchType at leftTypeStrengthens
                  rw [leftSuccess] at leftTypeStrengthens
                  cases motiveSuccess : motiveType.partialStrengthen?
                      strengthening.back with
                  | none =>
                      rw [motiveSuccess] at leftTypeStrengthens
                      cases leftTypeStrengthens
                  | some targetMotiveType =>
                      rw [motiveSuccess] at leftTypeStrengthens
                      cases leftTypeStrengthens
                      cases rightResult with
                      | mk targetRightBranchType targetRightRaw
                          targetRightTerm rightTypeStrengthens
                          rightRawStrengthens rightTypeRenames
                          rightRawRenames =>
                          change
                            Option.mapTwo
                              (rightType.partialStrengthen?
                                strengthening.back)
                              (motiveType.partialStrengthen?
                                strengthening.back)
                              Ty.arrow = some targetRightBranchType at rightTypeStrengthens
                          rw [rightSuccess, motiveSuccess] at rightTypeStrengthens
                          cases rightTypeStrengthens
                          exact {
                            targetType := targetMotiveType
                            targetRaw := RawTerm.eitherMatch
                              targetScrutineeRaw targetLeftRaw
                              targetRightRaw
                            targetTerm := Term.eitherMatch
                              targetScrutineeTerm targetLeftTerm
                              targetRightTerm
                            typeStrengthens := motiveSuccess
                            rawStrengthens := by
                              change
                                Option.mapThree
                                  (scrutineeRaw.partialStrengthen?
                                    strengthening.back)
                                  (leftRaw.partialStrengthen?
                                    strengthening.back)
                                  (rightRaw.partialStrengthen?
                                    strengthening.back)
                                  RawTerm.eitherMatch =
                                    some (RawTerm.eitherMatch
                                      targetScrutineeRaw targetLeftRaw
                                      targetRightRaw)
                              rw [scrutineeRawStrengthens,
                                leftRawStrengthens, rightRawStrengthens]
                              rfl
                            typeRenames :=
                              Ty.partialStrengthen?_imp_rename motiveType
                                strengthening.forward strengthening.back
                                strengthening.injectsBack targetMotiveType
                                motiveSuccess
                            rawRenames := by
                              cases scrutineeRawRenames
                              cases leftRawRenames
                              cases rightRawRenames
                              rfl
                          }

/-- Refinement introduction strengthens by strengthening its base value,
unit proof, and binder-indexed predicate raw. -/
def partialStrengthenTypedRefineIntro {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetPredicate : RawTerm (targetScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (predicateStrengthens :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    (baseResult : StrengtheningResult strengthening baseValue)
    (proofResult : StrengtheningResult strengthening predicateProof) :
    StrengtheningResult strengthening
      (Term.refineIntro predicate baseValue predicateProof) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm proofTypeStrengthens
      proofRawStrengthens proofTypeRenames proofRawRenames =>
      cases proofTypeStrengthens
      exact {
        targetType := Ty.refine baseResult.targetType targetPredicate
        targetRaw := RawTerm.refineIntro baseResult.targetRaw targetProofRaw
        targetTerm := Term.refineIntro targetPredicate baseResult.targetTerm
          targetProofTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (baseType.partialStrengthen? strengthening.back)
              (predicate.partialStrengthen? strengthening.back.lift)
              Ty.refine =
              some (Ty.refine baseResult.targetType targetPredicate)
          rw [baseResult.typeStrengthens, predicateStrengthens]
          rfl
        rawStrengthens := by
          change
            Option.mapTwo
              (valueRaw.partialStrengthen? strengthening.back)
              (proofRaw.partialStrengthen? strengthening.back)
              RawTerm.refineIntro =
              some (RawTerm.refineIntro baseResult.targetRaw targetProofRaw)
          rw [baseResult.rawStrengthens, proofRawStrengthens]
          rfl
        typeRenames :=
          Ty.partialStrengthen?_imp_rename
            (Ty.refine baseType predicate)
            strengthening.forward strengthening.back strengthening.injectsBack
            (Ty.refine baseResult.targetType targetPredicate)
            (by
              change
                Option.mapTwo
                  (baseType.partialStrengthen? strengthening.back)
                  (predicate.partialStrengthen? strengthening.back.lift)
                  Ty.refine =
                  some (Ty.refine baseResult.targetType targetPredicate)
              rw [baseResult.typeStrengthens, predicateStrengthens]
              rfl)
        rawRenames := by
          exact RawTerm.partialStrengthen?_imp_rename
            (RawTerm.refineIntro valueRaw proofRaw)
            strengthening.forward strengthening.back strengthening.injectsBack
            (RawTerm.refineIntro baseResult.targetRaw targetProofRaw)
            (by
              change
                Option.mapTwo
                  (valueRaw.partialStrengthen? strengthening.back)
                  (proofRaw.partialStrengthen? strengthening.back)
                  RawTerm.refineIntro =
                  some (RawTerm.refineIntro baseResult.targetRaw
                    targetProofRaw)
              rw [baseResult.rawStrengthens, proofRawStrengthens]
              rfl)
      }

/-- Refinement elimination strengthens by strengthening its refined
payload and projecting the strengthened base type out of the refined
type index. -/
def partialStrengthenTypedRefineElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (refinedResult : StrengtheningResult strengthening refinedValue) :
    StrengtheningResult strengthening (Term.refineElim refinedValue) := by
  cases refinedResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      change
        Option.mapTwo
          (baseType.partialStrengthen? strengthening.back)
          (predicate.partialStrengthen? strengthening.back.lift)
          Ty.refine = some targetType at typeStrengthens
      cases baseSuccess : baseType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [baseSuccess] at typeStrengthens
          cases typeStrengthens
      | some targetBaseType =>
          cases predicateSuccess : predicate.partialStrengthen?
              strengthening.back.lift with
          | none =>
              rw [baseSuccess, predicateSuccess] at typeStrengthens
              cases typeStrengthens
          | some targetPredicate =>
              rw [baseSuccess, predicateSuccess] at typeStrengthens
              cases typeStrengthens
              exact {
                targetType := targetBaseType
                targetRaw := RawTerm.refineElim targetRaw
                targetTerm := Term.refineElim targetTerm
                typeStrengthens := baseSuccess
                rawStrengthens := by
                  change
                    (match refinedRaw.partialStrengthen?
                        strengthening.back with
                    | some strengthenedRefined =>
                        some (RawTerm.refineElim strengthenedRefined)
                    | none => none) =
                      some (RawTerm.refineElim targetRaw)
                  rw [rawStrengthens]
                typeRenames :=
                  Ty.partialStrengthen?_imp_rename baseType
                    strengthening.forward strengthening.back
                    strengthening.injectsBack targetBaseType baseSuccess
                rawRenames := congrArg RawTerm.refineElim rawRenames
              }

/-- HoTT reflexivity strengthens by strengthening the carrier type and
the raw witness endpoint. -/
def partialStrengthenTypedRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningResult strengthening
      (Term.refl (context := sourceCtx) carrier rawWitness) where
  targetType := Ty.id targetCarrier targetWitness targetWitness
  targetRaw := RawTerm.refl targetWitness
  targetTerm := Term.refl (context := targetCtx) targetCarrier targetWitness
  typeStrengthens := by
    change
      Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        Ty.id =
        some (Ty.id targetCarrier targetWitness targetWitness)
    rw [carrierStrengthens, witnessStrengthens]
    rfl
  rawStrengthens := by
    change
      (match rawWitness.partialStrengthen? strengthening.back with
      | some strengthenedWitness => some (RawTerm.refl strengthenedWitness)
      | none => none) =
        some (RawTerm.refl targetWitness)
    rw [witnessStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename
      (Ty.id carrier rawWitness rawWitness)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.id targetCarrier targetWitness targetWitness)
      (by
        change
          Option.mapThree
            (carrier.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            Ty.id =
            some (Ty.id targetCarrier targetWitness targetWitness)
        rw [carrierStrengthens, witnessStrengthens]
        rfl)
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.refl rawWitness) strengthening.forward strengthening.back
      strengthening.injectsBack (RawTerm.refl targetWitness)
      (by
        change
          (match rawWitness.partialStrengthen? strengthening.back with
          | some strengthenedWitness => some (RawTerm.refl strengthenedWitness)
          | none => none) =
            some (RawTerm.refl targetWitness)
        rw [witnessStrengthens])

/-- Observational-equality reflexivity strengthens by strengthening the
carrier type and raw witness endpoint. -/
def partialStrengthenTypedOeqRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningResult strengthening
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) where
  targetType := Ty.oeq targetCarrier targetWitness targetWitness
  targetRaw := RawTerm.oeqRefl targetWitness
  targetTerm := Term.oeqRefl (context := targetCtx) targetCarrier targetWitness
  typeStrengthens := by
    change
      Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        Ty.oeq =
        some (Ty.oeq targetCarrier targetWitness targetWitness)
    rw [carrierStrengthens, witnessStrengthens]
    rfl
  rawStrengthens := by
    change
      (match rawWitness.partialStrengthen? strengthening.back with
      | some strengthenedWitness => some (RawTerm.oeqRefl strengthenedWitness)
      | none => none) =
        some (RawTerm.oeqRefl targetWitness)
    rw [witnessStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename
      (Ty.oeq carrier rawWitness rawWitness)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.oeq targetCarrier targetWitness targetWitness)
      (by
        change
          Option.mapThree
            (carrier.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            Ty.oeq =
            some (Ty.oeq targetCarrier targetWitness targetWitness)
        rw [carrierStrengthens, witnessStrengthens]
        rfl)
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.oeqRefl rawWitness) strengthening.forward strengthening.back
      strengthening.injectsBack (RawTerm.oeqRefl targetWitness)
      (by
        change
          (match rawWitness.partialStrengthen? strengthening.back with
          | some strengthenedWitness =>
              some (RawTerm.oeqRefl strengthenedWitness)
          | none => none) =
            some (RawTerm.oeqRefl targetWitness)
        rw [witnessStrengthens])

/-- Strict identity reflexivity strengthens by strengthening the carrier
type and raw witness endpoint, preserving the strict-mode evidence. -/
def partialStrengthenTypedIdStrictRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningResult strengthening
      (Term.idStrictRefl (context := sourceCtx) modeIsStrict
        carrier rawWitness) where
  targetType := Ty.idStrict targetCarrier targetWitness targetWitness
  targetRaw := RawTerm.idStrictRefl targetWitness
  targetTerm := Term.idStrictRefl (context := targetCtx) modeIsStrict
    targetCarrier targetWitness
  typeStrengthens := by
    change
      Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        (rawWitness.partialStrengthen? strengthening.back)
        Ty.idStrict =
        some (Ty.idStrict targetCarrier targetWitness targetWitness)
    rw [carrierStrengthens, witnessStrengthens]
    rfl
  rawStrengthens := by
    change
      (match rawWitness.partialStrengthen? strengthening.back with
      | some strengthenedWitness =>
          some (RawTerm.idStrictRefl strengthenedWitness)
      | none => none) =
        some (RawTerm.idStrictRefl targetWitness)
    rw [witnessStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename
      (Ty.idStrict carrier rawWitness rawWitness)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.idStrict targetCarrier targetWitness targetWitness)
      (by
        change
          Option.mapThree
            (carrier.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            (rawWitness.partialStrengthen? strengthening.back)
            Ty.idStrict =
            some (Ty.idStrict targetCarrier targetWitness targetWitness)
        rw [carrierStrengthens, witnessStrengthens]
        rfl)
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.idStrictRefl rawWitness) strengthening.forward
      strengthening.back strengthening.injectsBack
      (RawTerm.idStrictRefl targetWitness)
      (by
        change
          (match rawWitness.partialStrengthen? strengthening.back with
          | some strengthenedWitness =>
              some (RawTerm.idStrictRefl strengthenedWitness)
          | none => none) =
            some (RawTerm.idStrictRefl targetWitness)
        rw [witnessStrengthens])

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

/-- Universe-code terms strengthen through every context strengthening.

The raw universe code carries only the encoded inner universe level, so
no scope-indexed payload needs strengthening. -/
def partialStrengthenTypedUniverseCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    StrengtheningResult strengthening
      (Term.universeCode (context := sourceCtx) innerLevel outerLevel
        cumulOk levelLe) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.universeCode innerLevel.toNat
  targetTerm := Term.universeCode (context := targetCtx) innerLevel
    outerLevel cumulOk levelLe
  typeStrengthens := rfl
  rawStrengthens := rfl
  typeRenames := rfl
  rawRenames := rfl

/-- Arrow type-code terms strengthen by strengthening both schematic
raw payloads. -/
def partialStrengthenTypedArrowCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (targetDomainCodeRaw targetCodomainCodeRaw : RawTerm targetScope)
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back =
        some targetCodomainCodeRaw) :
    StrengtheningResult strengthening
      (Term.arrowCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw
  targetTerm := Term.arrowCode (context := targetCtx) outerLevel levelLe
    targetDomainCodeRaw targetCodomainCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (domainCodeRaw.partialStrengthen? strengthening.back)
        (codomainCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.arrowCode =
          some (RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw)
    rw [domainStrengthens, codomainStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.arrowCode domainCodeRaw codomainCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw)
      (by
        change
          Option.mapTwo
            (domainCodeRaw.partialStrengthen? strengthening.back)
            (codomainCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.arrowCode =
              some (RawTerm.arrowCode targetDomainCodeRaw targetCodomainCodeRaw)
        rw [domainStrengthens, codomainStrengthens]
        rfl)

/-- Dependent-Pi type-code terms strengthen by strengthening the domain
payload at the current context and the codomain payload under the lifted
context strengthening. -/
def partialStrengthenTypedPiTyCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningResult strengthening
      (Term.piTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw
  targetTerm := Term.piTyCode (context := targetCtx) outerLevel levelLe
    targetDomainCodeRaw targetCodomainCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (domainCodeRaw.partialStrengthen? strengthening.back)
        (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
        RawTerm.piTyCode =
          some (RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw)
    rw [domainStrengthens, codomainStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.piTyCode domainCodeRaw codomainCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw)
      (by
        change
          Option.mapTwo
            (domainCodeRaw.partialStrengthen? strengthening.back)
            (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
            RawTerm.piTyCode =
              some (RawTerm.piTyCode targetDomainCodeRaw targetCodomainCodeRaw)
        rw [domainStrengthens, codomainStrengthens]
        rfl)

/-- Dependent-Sigma type-code terms strengthen by strengthening the
domain payload at the current context and the codomain payload under the
lifted context strengthening. -/
def partialStrengthenTypedSigmaTyCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningResult strengthening
      (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.sigmaTyCode targetDomainCodeRaw targetCodomainCodeRaw
  targetTerm := Term.sigmaTyCode (context := targetCtx) outerLevel levelLe
    targetDomainCodeRaw targetCodomainCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (domainCodeRaw.partialStrengthen? strengthening.back)
        (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
        RawTerm.sigmaTyCode =
          some (RawTerm.sigmaTyCode targetDomainCodeRaw targetCodomainCodeRaw)
    rw [domainStrengthens, codomainStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.sigmaTyCode targetDomainCodeRaw targetCodomainCodeRaw)
      (by
        change
          Option.mapTwo
            (domainCodeRaw.partialStrengthen? strengthening.back)
            (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
            RawTerm.sigmaTyCode =
              some (RawTerm.sigmaTyCode targetDomainCodeRaw
                targetCodomainCodeRaw)
        rw [domainStrengthens, codomainStrengthens]
        rfl)

/-- Product type-code terms strengthen by strengthening both schematic
raw payloads. -/
def partialStrengthenTypedProductCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (targetFirstCodeRaw targetSecondCodeRaw : RawTerm targetScope)
    (firstStrengthens :
      firstCodeRaw.partialStrengthen? strengthening.back =
        some targetFirstCodeRaw)
    (secondStrengthens :
      secondCodeRaw.partialStrengthen? strengthening.back =
        some targetSecondCodeRaw) :
    StrengtheningResult strengthening
      (Term.productCode (context := sourceCtx) outerLevel levelLe
        firstCodeRaw secondCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw
  targetTerm := Term.productCode (context := targetCtx) outerLevel levelLe
    targetFirstCodeRaw targetSecondCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (firstCodeRaw.partialStrengthen? strengthening.back)
        (secondCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.productCode =
          some (RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw)
    rw [firstStrengthens, secondStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.productCode firstCodeRaw secondCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw)
      (by
        change
          Option.mapTwo
            (firstCodeRaw.partialStrengthen? strengthening.back)
            (secondCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.productCode =
              some (RawTerm.productCode targetFirstCodeRaw targetSecondCodeRaw)
        rw [firstStrengthens, secondStrengthens]
        rfl)

/-- Sum type-code terms strengthen by strengthening both schematic raw
payloads. -/
def partialStrengthenTypedSumCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningResult strengthening
      (Term.sumCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw
  targetTerm := Term.sumCode (context := targetCtx) outerLevel levelLe
    targetLeftCodeRaw targetRightCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (leftCodeRaw.partialStrengthen? strengthening.back)
        (rightCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.sumCode =
          some (RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw)
    rw [leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.sumCode leftCodeRaw rightCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw)
      (by
        change
          Option.mapTwo
            (leftCodeRaw.partialStrengthen? strengthening.back)
            (rightCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.sumCode =
              some (RawTerm.sumCode targetLeftCodeRaw targetRightCodeRaw)
        rw [leftStrengthens, rightStrengthens]
        rfl)

/-- List type-code terms strengthen by strengthening their schematic
element-code payload. -/
def partialStrengthenTypedListCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningResult strengthening
      (Term.listCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.listCode targetElementCodeRaw
  targetTerm := Term.listCode (context := targetCtx) outerLevel levelLe
    targetElementCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      (match elementCodeRaw.partialStrengthen? strengthening.back with
      | some strengthenedElement => some (RawTerm.listCode strengthenedElement)
      | none => none) = some (RawTerm.listCode targetElementCodeRaw)
    rw [elementStrengthens]
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.listCode elementCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.listCode targetElementCodeRaw)
      (by
        change
          (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (RawTerm.listCode strengthenedElement)
          | none => none) = some (RawTerm.listCode targetElementCodeRaw)
        rw [elementStrengthens])

/-- Option type-code terms strengthen by strengthening their schematic
element-code payload. -/
def partialStrengthenTypedOptionCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningResult strengthening
      (Term.optionCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.optionCode targetElementCodeRaw
  targetTerm := Term.optionCode (context := targetCtx) outerLevel levelLe
    targetElementCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      (match elementCodeRaw.partialStrengthen? strengthening.back with
      | some strengthenedElement =>
          some (RawTerm.optionCode strengthenedElement)
      | none => none) = some (RawTerm.optionCode targetElementCodeRaw)
    rw [elementStrengthens]
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.optionCode elementCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.optionCode targetElementCodeRaw)
      (by
        change
          (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (RawTerm.optionCode strengthenedElement)
          | none => none) = some (RawTerm.optionCode targetElementCodeRaw)
        rw [elementStrengthens])

/-- Either type-code terms strengthen by strengthening both schematic
raw payloads. -/
def partialStrengthenTypedEitherCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningResult strengthening
      (Term.eitherCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw
  targetTerm := Term.eitherCode (context := targetCtx) outerLevel levelLe
    targetLeftCodeRaw targetRightCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (leftCodeRaw.partialStrengthen? strengthening.back)
        (rightCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.eitherCode =
          some (RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw)
    rw [leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.eitherCode leftCodeRaw rightCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw)
      (by
        change
          Option.mapTwo
            (leftCodeRaw.partialStrengthen? strengthening.back)
            (rightCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.eitherCode =
              some (RawTerm.eitherCode targetLeftCodeRaw targetRightCodeRaw)
        rw [leftStrengthens, rightStrengthens]
        rfl)

/-- Identity type-code terms strengthen by strengthening the carrier
code and both schematic endpoint payloads. -/
def partialStrengthenTypedIdCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (targetTypeCodeRaw targetLeftRaw targetRightRaw : RawTerm targetScope)
    (typeCodeStrengthens :
      typeCodeRaw.partialStrengthen? strengthening.back =
        some targetTypeCodeRaw)
    (leftStrengthens :
      leftRaw.partialStrengthen? strengthening.back =
        some targetLeftRaw)
    (rightStrengthens :
      rightRaw.partialStrengthen? strengthening.back =
        some targetRightRaw) :
    StrengtheningResult strengthening
      (Term.idCode (context := sourceCtx) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.idCode targetTypeCodeRaw targetLeftRaw targetRightRaw
  targetTerm := Term.idCode (context := targetCtx) outerLevel levelLe
    targetTypeCodeRaw targetLeftRaw targetRightRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapThree
        (typeCodeRaw.partialStrengthen? strengthening.back)
        (leftRaw.partialStrengthen? strengthening.back)
        (rightRaw.partialStrengthen? strengthening.back)
        RawTerm.idCode =
          some (RawTerm.idCode targetTypeCodeRaw targetLeftRaw targetRightRaw)
    rw [typeCodeStrengthens, leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.idCode typeCodeRaw leftRaw rightRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.idCode targetTypeCodeRaw targetLeftRaw targetRightRaw)
      (by
        change
          Option.mapThree
            (typeCodeRaw.partialStrengthen? strengthening.back)
            (leftRaw.partialStrengthen? strengthening.back)
            (rightRaw.partialStrengthen? strengthening.back)
            RawTerm.idCode =
              some (RawTerm.idCode targetTypeCodeRaw targetLeftRaw
                targetRightRaw)
        rw [typeCodeStrengthens, leftStrengthens, rightStrengthens]
        rfl)

/-- Equivalence type-code terms strengthen by strengthening both
schematic type-code payloads. -/
def partialStrengthenTypedEquivCode {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (targetLeftTypeCodeRaw targetRightTypeCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftTypeCodeRaw)
    (rightStrengthens :
      rightTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetRightTypeCodeRaw) :
    StrengtheningResult strengthening
      (Term.equivCode (context := sourceCtx) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) where
  targetType := Ty.universe outerLevel levelLe
  targetRaw := RawTerm.equivCode targetLeftTypeCodeRaw targetRightTypeCodeRaw
  targetTerm := Term.equivCode (context := targetCtx) outerLevel levelLe
    targetLeftTypeCodeRaw targetRightTypeCodeRaw
  typeStrengthens := rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (leftTypeCodeRaw.partialStrengthen? strengthening.back)
        (rightTypeCodeRaw.partialStrengthen? strengthening.back)
        RawTerm.equivCode =
          some (RawTerm.equivCode targetLeftTypeCodeRaw
            targetRightTypeCodeRaw)
    rw [leftStrengthens, rightStrengthens]
    rfl
  typeRenames := rfl
  rawRenames :=
    RawTerm.partialStrengthen?_imp_rename
      (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw)
      strengthening.forward strengthening.back strengthening.injectsBack
      (RawTerm.equivCode targetLeftTypeCodeRaw targetRightTypeCodeRaw)
      (by
        change
          Option.mapTwo
            (leftTypeCodeRaw.partialStrengthen? strengthening.back)
            (rightTypeCodeRaw.partialStrengthen? strengthening.back)
            RawTerm.equivCode =
              some (RawTerm.equivCode targetLeftTypeCodeRaw
                targetRightTypeCodeRaw)
        rw [leftStrengthens, rightStrengthens]
        rfl)

end Term

end LeanFX2
