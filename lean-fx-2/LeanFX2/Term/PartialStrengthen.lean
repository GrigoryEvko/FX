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

/-- Boolean eliminator strengthens by strengthening the scrutinee and
both branches, then rebuilding each motive substitution through the
single-binder strengthening/substitution bridge. -/
def partialStrengthenTypedBoolElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    {targetMotiveType : Ty level (targetScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (motiveStrengthens :
      motiveType.partialStrengthen? strengthening.back.lift =
        some targetMotiveType)
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (thenResult : StrengtheningResult strengthening thenBranch)
    (elseResult : StrengtheningResult strengthening elseBranch) :
    StrengtheningResult strengthening
      (Term.boolElim scrutinee thenBranch elseBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      cases scrutineeTypeStrengthens
      cases thenResult with
      | mk targetThenType targetThenRaw targetThenTerm thenTypeStrengthens
          thenRawStrengthens thenTypeRenames thenRawRenames =>
          have thenTypeExpected :
              (motiveType.subst0 Ty.bool
                  RawTerm.boolTrue).partialStrengthen?
                strengthening.back =
                some (targetMotiveType.subst0 Ty.bool
                  RawTerm.boolTrue) :=
            Ty.partialStrengthen?_subst0_of_success motiveType
              targetMotiveType Ty.bool Ty.bool RawTerm.boolTrue
              RawTerm.boolTrue strengthening.forward strengthening.back
              strengthening.injectsBack strengthening.back_forward
              motiveStrengthens rfl rfl
          rw [thenTypeExpected] at thenTypeStrengthens
          cases thenTypeStrengthens
          cases elseResult with
          | mk targetElseType targetElseRaw targetElseTerm elseTypeStrengthens
              elseRawStrengthens elseTypeRenames elseRawRenames =>
              have elseTypeExpected :
                  (motiveType.subst0 Ty.bool
                      RawTerm.boolFalse).partialStrengthen?
                    strengthening.back =
                    some (targetMotiveType.subst0 Ty.bool
                      RawTerm.boolFalse) :=
                Ty.partialStrengthen?_subst0_of_success motiveType
                  targetMotiveType Ty.bool Ty.bool RawTerm.boolFalse
                  RawTerm.boolFalse strengthening.forward strengthening.back
                  strengthening.injectsBack strengthening.back_forward
                  motiveStrengthens rfl rfl
              rw [elseTypeExpected] at elseTypeStrengthens
              cases elseTypeStrengthens
              have resultTypeStrengthens :
                  (motiveType.subst0 Ty.bool scrutineeRaw).partialStrengthen?
                    strengthening.back =
                    some (targetMotiveType.subst0 Ty.bool
                      targetScrutineeRaw) :=
                Ty.partialStrengthen?_subst0_of_success motiveType
                  targetMotiveType Ty.bool Ty.bool scrutineeRaw
                  targetScrutineeRaw strengthening.forward strengthening.back
                  strengthening.injectsBack strengthening.back_forward
                  motiveStrengthens rfl scrutineeRawStrengthens
              exact {
                targetType := targetMotiveType.subst0 Ty.bool
                  targetScrutineeRaw
                targetRaw := RawTerm.boolElim targetScrutineeRaw
                  targetThenRaw targetElseRaw
                targetTerm := Term.boolElim targetScrutineeTerm
                  targetThenTerm targetElseTerm
                typeStrengthens := resultTypeStrengthens
                rawStrengthens := by
                  change
                    Option.mapThree
                      (scrutineeRaw.partialStrengthen? strengthening.back)
                      (thenRaw.partialStrengthen? strengthening.back)
                      (elseRaw.partialStrengthen? strengthening.back)
                      RawTerm.boolElim =
                        some (RawTerm.boolElim targetScrutineeRaw
                          targetThenRaw targetElseRaw)
                  rw [scrutineeRawStrengthens, thenRawStrengthens,
                    elseRawStrengthens]
                  rfl
                typeRenames :=
                  Ty.partialStrengthen?_imp_rename
                    (motiveType.subst0 Ty.bool scrutineeRaw)
                    strengthening.forward strengthening.back
                    strengthening.injectsBack
                    (targetMotiveType.subst0 Ty.bool targetScrutineeRaw)
                    resultTypeStrengthens
                rawRenames := by
                  cases scrutineeRawRenames
                  cases thenRawRenames
                  cases elseRawRenames
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

/-- Success branch for non-dependent application strengthening.

This helper keeps the computational target term out of the `Option` and
equality-recursion dispatcher used by `partialStrengthenTypedApp`, giving
the soundness proof a stable term to target. -/
def partialStrengthenTypedAppOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {targetFunctionRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (targetFunctionTerm :
      Term targetCtx (Ty.arrow targetDomainType targetCodomainType)
        targetFunctionRaw)
    (targetArgumentTerm :
      Term targetCtx targetDomainType targetArgumentRaw)
    (_domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (functionRawStrengthens :
      functionRaw.partialStrengthen? strengthening.back =
        some targetFunctionRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (functionRawRenames :
      functionRaw = targetFunctionRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.app functionTerm argumentTerm) := {
  targetType := targetCodomainType
  targetRaw := RawTerm.app targetFunctionRaw targetArgumentRaw
  targetTerm := Term.app targetFunctionTerm targetArgumentTerm
  typeStrengthens := codomainSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (functionRaw.partialStrengthen? strengthening.back)
        (argumentRaw.partialStrengthen? strengthening.back)
        RawTerm.app =
        some (RawTerm.app targetFunctionRaw targetArgumentRaw)
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

/-- Non-dependent function application strengthens by strengthening the
function and argument, then decomposing the strengthened arrow type. -/
def partialStrengthenTypedApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
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
      rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
      cases functionTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [domainSuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedAppOfSuccess
            targetFunctionTerm targetArgumentTerm domainSuccess
            codomainSuccess functionRawStrengthens
            argumentRawStrengthens functionRawRenames argumentRawRenames

/-- Success branch for dependent application strengthening.

The dependent result type is computed from explicit domain/codomain and
argument strengthening successes, avoiding a proof-dependent dispatcher in
the soundness layer. -/
def partialStrengthenTypedAppPiOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {targetCodomainType : Ty level (targetScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {targetFunctionRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (targetFunctionTerm :
      Term targetCtx (Ty.piTy targetDomainType targetCodomainType)
        targetFunctionRaw)
    (targetArgumentTerm : Term targetCtx targetDomainType
      targetArgumentRaw)
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back.lift =
        some targetCodomainType)
    (functionRawStrengthens :
      functionRaw.partialStrengthen? strengthening.back =
        some targetFunctionRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (functionRawRenames :
      functionRaw = targetFunctionRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.appPi functionTerm argumentTerm) := by
  have resultTypeStrengthens :
      (codomainType.subst0 domainType argumentRaw).partialStrengthen?
        strengthening.back =
        some (targetCodomainType.subst0 targetDomainType
          targetArgumentRaw) :=
    Ty.partialStrengthen?_subst0_of_success codomainType
      targetCodomainType domainType targetDomainType argumentRaw
      targetArgumentRaw strengthening.forward strengthening.back
      strengthening.injectsBack strengthening.back_forward codomainSuccess
      domainSuccess argumentRawStrengthens
  exact {
    targetType := targetCodomainType.subst0 targetDomainType
      targetArgumentRaw
    targetRaw := RawTerm.app targetFunctionRaw targetArgumentRaw
    targetTerm := Term.appPi targetFunctionTerm targetArgumentTerm
    typeStrengthens := resultTypeStrengthens
    rawStrengthens := by
      change
        Option.mapTwo
          (functionRaw.partialStrengthen? strengthening.back)
          (argumentRaw.partialStrengthen? strengthening.back)
          RawTerm.app =
          some (RawTerm.app targetFunctionRaw targetArgumentRaw)
      rw [functionRawStrengthens, argumentRawStrengthens]
      rfl
    typeRenames :=
      Ty.partialStrengthen?_imp_rename
        (codomainType.subst0 domainType argumentRaw)
        strengthening.forward strengthening.back strengthening.injectsBack
        (targetCodomainType.subst0 targetDomainType targetArgumentRaw)
        resultTypeStrengthens
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
    {targetDomainType : Ty level targetScope}
    {targetCodomainType : Ty level (targetScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back.lift =
        some targetCodomainType)
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
      rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
      cases functionTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [domainSuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedAppPiOfSuccess
            targetFunctionTerm targetArgumentTerm domainSuccess
            codomainSuccess functionRawStrengthens
            argumentRawStrengthens functionRawRenames argumentRawRenames

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

/-- Pre-witnessed cubical path-application strengthening.

Replaces the wrapper's dual `Option.casesOn` on
`Ty.path`'s carrier + leftEndpoint + rightEndpoint pivots with
explicit `carrierSuccess`/`leftSuccess`/`rightSuccess` witnesses.

The unused `leftSuccess`/`rightSuccess` are kept in the signature
(prefixed `_`) so the OfSuccess-sound theorem can recover the
endpoint renaming equalities used by `pathApp_HEq_congr`. -/
def partialStrengthenTypedPathAppOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {targetPathRaw targetIntervalRaw : RawTerm targetScope}
    {pathTerm :
      Term sourceCtx
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (targetPathTerm :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetPathRaw)
    (targetIntervalTerm :
      Term targetCtx Ty.interval targetIntervalRaw)
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (pathRawStrengthens :
      pathRaw.partialStrengthen? strengthening.back = some targetPathRaw)
    (intervalRawStrengthens :
      intervalRaw.partialStrengthen? strengthening.back =
        some targetIntervalRaw)
    (pathRawRenames :
      pathRaw = targetPathRaw.rename strengthening.forward)
    (intervalRawRenames :
      intervalRaw = targetIntervalRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) where
  targetType := targetCarrierType
  targetRaw := RawTerm.pathApp targetPathRaw targetIntervalRaw
  targetTerm :=
    Term.pathApp modeIsUnivalent targetPathTerm targetIntervalTerm
  typeStrengthens := carrierSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (pathRaw.partialStrengthen? strengthening.back)
        (intervalRaw.partialStrengthen? strengthening.back)
        RawTerm.pathApp =
        some (RawTerm.pathApp targetPathRaw targetIntervalRaw)
    rw [pathRawStrengthens, intervalRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierSuccess
  rawRenames := by
    cases pathRawRenames
    cases intervalRawRenames
    rfl

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

/-- Success branch for list-eliminator strengthening.

Takes pre-decomposed element/motive successes plus the explicit
target raw and term components.  Construction is term-mode and reduces
fully under `dsimp` — soundness can be proved without unfolding through
the wrapper's internal `cases h :` discriminator. -/
def partialStrengthenTypedListElimOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {targetElementType targetMotiveType : Ty level targetScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {targetScrutineeRaw targetNilRaw targetConsRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (targetScrutineeTerm :
      Term targetCtx (Ty.listType targetElementType) targetScrutineeRaw)
    (targetNilTerm : Term targetCtx targetMotiveType targetNilRaw)
    (targetConsTerm :
      Term targetCtx
        (Ty.arrow targetElementType
          (Ty.arrow (Ty.listType targetElementType) targetMotiveType))
        targetConsRaw)
    (_elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType)
    (motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (scrutineeRawStrengthens :
      scrutineeRaw.partialStrengthen? strengthening.back =
        some targetScrutineeRaw)
    (nilRawStrengthens :
      nilRaw.partialStrengthen? strengthening.back = some targetNilRaw)
    (consRawStrengthens :
      consRaw.partialStrengthen? strengthening.back = some targetConsRaw)
    (scrutineeRawRenames :
      scrutineeRaw = targetScrutineeRaw.rename strengthening.forward)
    (nilRawRenames :
      nilRaw = targetNilRaw.rename strengthening.forward)
    (consRawRenames :
      consRaw = targetConsRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.listElim scrutinee nilBranch consBranch) := {
  targetType := targetMotiveType
  targetRaw := RawTerm.listElim targetScrutineeRaw targetNilRaw
    targetConsRaw
  targetTerm := Term.listElim targetScrutineeTerm targetNilTerm
    targetConsTerm
  typeStrengthens := motiveSuccess
  rawStrengthens := by
    change
      Option.mapThree
        (scrutineeRaw.partialStrengthen? strengthening.back)
        (nilRaw.partialStrengthen? strengthening.back)
        (consRaw.partialStrengthen? strengthening.back)
        RawTerm.listElim =
        some (RawTerm.listElim targetScrutineeRaw targetNilRaw
          targetConsRaw)
    rw [scrutineeRawStrengthens, nilRawStrengthens, consRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename motiveType strengthening.forward
      strengthening.back strengthening.injectsBack targetMotiveType
      motiveSuccess
  rawRenames := by
    cases scrutineeRawRenames
    cases nilRawRenames
    cases consRawRenames
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
                  exact partialStrengthenTypedListElimOfSuccess
                    targetScrutineeTerm targetNilTerm targetConsTerm
                    elementSuccess nilTypeStrengthens
                    scrutineeRawStrengthens nilRawStrengthens
                    consRawStrengthens scrutineeRawRenames nilRawRenames
                    consRawRenames

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

/-- Success branch for option-match strengthening.  Pure term-mode
construction; see `partialStrengthenTypedListElimOfSuccess` rationale. -/
def partialStrengthenTypedOptionMatchOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {targetElementType targetMotiveType : Ty level targetScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {targetScrutineeRaw targetNoneRaw targetSomeRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (targetScrutineeTerm :
      Term targetCtx (Ty.optionType targetElementType)
        targetScrutineeRaw)
    (targetNoneTerm : Term targetCtx targetMotiveType targetNoneRaw)
    (targetSomeTerm :
      Term targetCtx (Ty.arrow targetElementType targetMotiveType)
        targetSomeRaw)
    (_elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType)
    (motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (scrutineeRawStrengthens :
      scrutineeRaw.partialStrengthen? strengthening.back =
        some targetScrutineeRaw)
    (noneRawStrengthens :
      noneRaw.partialStrengthen? strengthening.back = some targetNoneRaw)
    (someRawStrengthens :
      someRaw.partialStrengthen? strengthening.back = some targetSomeRaw)
    (scrutineeRawRenames :
      scrutineeRaw = targetScrutineeRaw.rename strengthening.forward)
    (noneRawRenames :
      noneRaw = targetNoneRaw.rename strengthening.forward)
    (someRawRenames :
      someRaw = targetSomeRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.optionMatch scrutinee noneBranch someBranch) := {
  targetType := targetMotiveType
  targetRaw := RawTerm.optionMatch targetScrutineeRaw targetNoneRaw
    targetSomeRaw
  targetTerm := Term.optionMatch targetScrutineeTerm targetNoneTerm
    targetSomeTerm
  typeStrengthens := motiveSuccess
  rawStrengthens := by
    change
      Option.mapThree
        (scrutineeRaw.partialStrengthen? strengthening.back)
        (noneRaw.partialStrengthen? strengthening.back)
        (someRaw.partialStrengthen? strengthening.back)
        RawTerm.optionMatch =
        some (RawTerm.optionMatch targetScrutineeRaw targetNoneRaw
          targetSomeRaw)
    rw [scrutineeRawStrengthens, noneRawStrengthens, someRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename motiveType strengthening.forward
      strengthening.back strengthening.injectsBack targetMotiveType
      motiveSuccess
  rawRenames := by
    cases scrutineeRawRenames
    cases noneRawRenames
    cases someRawRenames
    rfl
}

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
                  exact partialStrengthenTypedOptionMatchOfSuccess
                    targetScrutineeTerm targetNoneTerm targetSomeTerm
                    elementSuccess noneTypeStrengthens
                    scrutineeRawStrengthens noneRawStrengthens
                    someRawStrengthens scrutineeRawRenames noneRawRenames
                    someRawRenames

/-- Success branch for either-match strengthening.  Pure term-mode
construction; see `partialStrengthenTypedListElimOfSuccess` rationale. -/
def partialStrengthenTypedEitherMatchOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {targetLeftType targetRightType targetMotiveType : Ty level targetScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {targetScrutineeRaw targetLeftRaw targetRightRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (targetScrutineeTerm :
      Term targetCtx (Ty.eitherType targetLeftType targetRightType)
        targetScrutineeRaw)
    (targetLeftTerm :
      Term targetCtx (Ty.arrow targetLeftType targetMotiveType)
        targetLeftRaw)
    (targetRightTerm :
      Term targetCtx (Ty.arrow targetRightType targetMotiveType)
        targetRightRaw)
    (_leftSuccess :
      leftType.partialStrengthen? strengthening.back =
        some targetLeftType)
    (_rightSuccess :
      rightType.partialStrengthen? strengthening.back =
        some targetRightType)
    (motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (scrutineeRawStrengthens :
      scrutineeRaw.partialStrengthen? strengthening.back =
        some targetScrutineeRaw)
    (leftRawStrengthens :
      leftRaw.partialStrengthen? strengthening.back = some targetLeftRaw)
    (rightRawStrengthens :
      rightRaw.partialStrengthen? strengthening.back =
        some targetRightRaw)
    (scrutineeRawRenames :
      scrutineeRaw = targetScrutineeRaw.rename strengthening.forward)
    (leftRawRenames :
      leftRaw = targetLeftRaw.rename strengthening.forward)
    (rightRawRenames :
      rightRaw = targetRightRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.eitherMatch scrutinee leftBranch rightBranch) := {
  targetType := targetMotiveType
  targetRaw := RawTerm.eitherMatch targetScrutineeRaw targetLeftRaw
    targetRightRaw
  targetTerm := Term.eitherMatch targetScrutineeTerm targetLeftTerm
    targetRightTerm
  typeStrengthens := motiveSuccess
  rawStrengthens := by
    change
      Option.mapThree
        (scrutineeRaw.partialStrengthen? strengthening.back)
        (leftRaw.partialStrengthen? strengthening.back)
        (rightRaw.partialStrengthen? strengthening.back)
        RawTerm.eitherMatch =
        some (RawTerm.eitherMatch targetScrutineeRaw targetLeftRaw
          targetRightRaw)
    rw [scrutineeRawStrengthens, leftRawStrengthens, rightRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename motiveType strengthening.forward
      strengthening.back strengthening.injectsBack targetMotiveType
      motiveSuccess
  rawRenames := by
    cases scrutineeRawRenames
    cases leftRawRenames
    cases rightRawRenames
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
                          exact partialStrengthenTypedEitherMatchOfSuccess
                            targetScrutineeTerm targetLeftTerm
                            targetRightTerm leftSuccess rightSuccess
                            motiveSuccess scrutineeRawStrengthens
                            leftRawStrengthens rightRawStrengthens
                            scrutineeRawRenames leftRawRenames
                            rightRawRenames

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

/-- Success branch for refinement-elimination strengthening.

Takes pre-decomposed witnesses for the base type, predicate, and the
strengthened refined-value term.  Splits out the term-mode body so the
strengthening-image soundness layer can prove the soundness theorem
without traversing `Option.casesOn` on the `partialStrengthen?` pivots
inside the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedRefineElimOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {targetRefinedRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (targetRefinedTerm :
      Term targetCtx (Ty.refine targetBaseType targetPredicate)
        targetRefinedRaw)
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (_predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    (refinedRawStrengthens :
      refinedRaw.partialStrengthen? strengthening.back =
        some targetRefinedRaw)
    (refinedRawRenames :
      refinedRaw = targetRefinedRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.refineElim refinedValue) := {
  targetType := targetBaseType
  targetRaw := RawTerm.refineElim targetRefinedRaw
  targetTerm := Term.refineElim targetRefinedTerm
  typeStrengthens := baseSuccess
  rawStrengthens := by
    change
      (match refinedRaw.partialStrengthen? strengthening.back with
        | some strengthenedRefined =>
            some (RawTerm.refineElim strengthenedRefined)
        | none => none) =
        some (RawTerm.refineElim targetRefinedRaw)
    rw [refinedRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  rawRenames := by
    cases refinedRawRenames
    rfl
}

/-- Refinement elimination strengthens by strengthening its refined
payload and projecting the strengthened base type out of the refined
type index.

App-pattern: takes the base-type and predicate strengthening witnesses
`baseSuccess` / `predicateSuccess` as explicit parameters, lifted from
the dispatcher's nested option-splits.  The body destructures the
refined value's `StrengtheningResult`, aligns the `Ty.refine` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedRefineElimOfSuccess`.  This shape admits a
clean App-pattern soundness proof
(`partialStrengthenTypedRefineElim_sound`) by mirror-destructure +
final-arm `OfSuccess_sound` delegation. -/
def partialStrengthenTypedRefineElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    (refinedResult : StrengtheningResult strengthening refinedValue) :
    StrengtheningResult strengthening (Term.refineElim refinedValue) := by
  cases refinedResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have expectedRefineTypeStrengthens :
          (Ty.refine baseType predicate).partialStrengthen? strengthening.back =
            some (Ty.refine targetBaseType targetPredicate) := by
        change
          Option.mapTwo
            (baseType.partialStrengthen? strengthening.back)
            (predicate.partialStrengthen? strengthening.back.lift)
            Ty.refine =
              some (Ty.refine targetBaseType targetPredicate)
        rw [baseSuccess, predicateSuccess]
        rfl
      rw [expectedRefineTypeStrengthens] at typeStrengthens
      cases typeStrengthens
      exact partialStrengthenTypedRefineElimOfSuccess
        targetTerm baseSuccess predicateSuccess rawStrengthens rawRenames

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

/-- Success branch for identity-elimination strengthening.

Takes pre-decomposed witnesses for the carrier, left endpoint, right
endpoint of the witness's identity type, plus the strengthened
base-case and witness-term values.  Splits out the term-mode body so
the strengthening-image soundness layer can prove the soundness
theorem without traversing `Option.casesOn` on the three
`partialStrengthen?` pivots (carrier / leftEndpoint / rightEndpoint)
inside the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedIdJOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw)
    (targetWitnessTerm :
      Term targetCtx
        (Ty.id targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw)
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.idJ baseCase witness) where
  targetType := targetMotiveType
  targetRaw := RawTerm.idJ targetBaseRaw targetWitnessRaw
  targetTerm := Term.idJ targetBaseTerm targetWitnessTerm
  typeStrengthens := baseTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (baseRaw.partialStrengthen? strengthening.back)
        (witnessRaw.partialStrengthen? strengthening.back)
        RawTerm.idJ =
          some (RawTerm.idJ targetBaseRaw targetWitnessRaw)
    rw [baseRawStrengthens, witnessRawStrengthens]
    rfl
  typeRenames := baseTypeRenames
  rawRenames := by
    cases baseRawRenames
    cases witnessRawRenames
    rfl

/-- Identity eliminator strengthens by strengthening its base case and
witness, then decomposing the strengthened identity type carried by the
witness. -/
def partialStrengthenTypedIdJ {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseResult : StrengtheningResult strengthening baseCase)
    (witnessResult : StrengtheningResult strengthening witness) :
    StrengtheningResult strengthening (Term.idJ baseCase witness) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          change
            Option.mapThree
              (carrier.partialStrengthen? strengthening.back)
              (leftEndpoint.partialStrengthen? strengthening.back)
              (rightEndpoint.partialStrengthen? strengthening.back)
              Ty.id = some targetWitnessType at witnessTypeStrengthens
          cases carrierSuccess : carrier.partialStrengthen?
              strengthening.back with
          | none =>
              rw [carrierSuccess] at witnessTypeStrengthens
              cases witnessTypeStrengthens
          | some targetCarrier =>
              cases leftSuccess : leftEndpoint.partialStrengthen?
                  strengthening.back with
              | none =>
                  rw [carrierSuccess, leftSuccess] at witnessTypeStrengthens
                  cases witnessTypeStrengthens
              | some targetLeftEndpoint =>
                  cases rightSuccess : rightEndpoint.partialStrengthen?
                      strengthening.back with
                  | none =>
                      rw [carrierSuccess, leftSuccess, rightSuccess] at witnessTypeStrengthens
                      cases witnessTypeStrengthens
                  | some targetRightEndpoint =>
                      rw [carrierSuccess, leftSuccess, rightSuccess] at witnessTypeStrengthens
                      cases witnessTypeStrengthens
                      exact partialStrengthenTypedIdJOfSuccess
                        targetBaseTerm targetWitnessTerm baseTypeStrengthens
                        carrierSuccess leftSuccess rightSuccess
                        baseRawStrengthens witnessRawStrengthens
                        baseTypeRenames baseRawRenames witnessRawRenames

/-- Success branch for observational-equality elimination strengthening.
Mirrors `partialStrengthenTypedIdJOfSuccess`: pre-decomposed witnesses
for the observational equality's carrier/leftEndpoint/rightEndpoint
pivots, plus strengthened base-case and witness-term values.  Allows
soundness to apply `Term.oeqJ_HEq_congr` without traversing the
wrapper's triple `Option.casesOn` discriminator wall. -/
def partialStrengthenTypedOeqJOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw)
    (targetWitnessTerm :
      Term targetCtx
        (Ty.oeq targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw)
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (_carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.oeqJ baseCase witness) where
  targetType := targetMotiveType
  targetRaw := RawTerm.oeqJ targetBaseRaw targetWitnessRaw
  targetTerm := Term.oeqJ targetBaseTerm targetWitnessTerm
  typeStrengthens := baseTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (baseRaw.partialStrengthen? strengthening.back)
        (witnessRaw.partialStrengthen? strengthening.back)
        RawTerm.oeqJ =
          some (RawTerm.oeqJ targetBaseRaw targetWitnessRaw)
    rw [baseRawStrengthens, witnessRawStrengthens]
    rfl
  typeRenames := baseTypeRenames
  rawRenames := by
    cases baseRawRenames
    cases witnessRawRenames
    rfl

/-- Observational-equality eliminator strengthens by strengthening its
base case and witness, then decomposing the strengthened observational
equality type carried by the witness. -/
def partialStrengthenTypedOeqJ {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseResult : StrengtheningResult strengthening baseCase)
    (witnessResult : StrengtheningResult strengthening witness) :
    StrengtheningResult strengthening (Term.oeqJ baseCase witness) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          change
            Option.mapThree
              (carrier.partialStrengthen? strengthening.back)
              (leftEndpoint.partialStrengthen? strengthening.back)
              (rightEndpoint.partialStrengthen? strengthening.back)
              Ty.oeq = some targetWitnessType at witnessTypeStrengthens
          cases carrierSuccess : carrier.partialStrengthen?
              strengthening.back with
          | none =>
              rw [carrierSuccess] at witnessTypeStrengthens
              cases witnessTypeStrengthens
          | some targetCarrier =>
              cases leftSuccess : leftEndpoint.partialStrengthen?
                  strengthening.back with
              | none =>
                  rw [carrierSuccess, leftSuccess] at witnessTypeStrengthens
                  cases witnessTypeStrengthens
              | some targetLeftEndpoint =>
                  cases rightSuccess : rightEndpoint.partialStrengthen?
                      strengthening.back with
                  | none =>
                      rw [carrierSuccess, leftSuccess, rightSuccess] at witnessTypeStrengthens
                      cases witnessTypeStrengthens
                  | some targetRightEndpoint =>
                      rw [carrierSuccess, leftSuccess, rightSuccess] at witnessTypeStrengthens
                      cases witnessTypeStrengthens
                      exact partialStrengthenTypedOeqJOfSuccess
                        targetBaseTerm targetWitnessTerm baseTypeStrengthens
                        carrierSuccess leftSuccess rightSuccess
                        baseRawStrengthens witnessRawStrengthens
                        baseTypeRenames baseRawRenames witnessRawRenames

/-- Success branch for strict-identity recursor strengthening.  Mirrors
`partialStrengthenTypedIdJOfSuccess` with the strict-identity carrier
shape and the `modeIsStrict` evidence. -/
def partialStrengthenTypedIdStrictRecOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw)
    (targetWitnessTerm :
      Term targetCtx
        (Ty.idStrict targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw)
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (_carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.idStrictRec modeIsStrict baseCase witness) where
  targetType := targetMotiveType
  targetRaw := RawTerm.idStrictRec targetBaseRaw targetWitnessRaw
  targetTerm := Term.idStrictRec modeIsStrict targetBaseTerm
    targetWitnessTerm
  typeStrengthens := baseTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (baseRaw.partialStrengthen? strengthening.back)
        (witnessRaw.partialStrengthen? strengthening.back)
        RawTerm.idStrictRec =
          some (RawTerm.idStrictRec targetBaseRaw targetWitnessRaw)
    rw [baseRawStrengthens, witnessRawStrengthens]
    rfl
  typeRenames := baseTypeRenames
  rawRenames := by
    cases baseRawRenames
    cases witnessRawRenames
    rfl

/-- Strict-identity recursor strengthens by strengthening its base case
and witness, then decomposing the strengthened strict identity type
carried by the witness. -/
def partialStrengthenTypedIdStrictRec {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseResult : StrengtheningResult strengthening baseCase)
    (witnessResult : StrengtheningResult strengthening witness) :
    StrengtheningResult strengthening
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          change
            Option.mapThree
              (carrier.partialStrengthen? strengthening.back)
              (leftEndpoint.partialStrengthen? strengthening.back)
              (rightEndpoint.partialStrengthen? strengthening.back)
              Ty.idStrict = some targetWitnessType at witnessTypeStrengthens
          cases carrierSuccess : carrier.partialStrengthen?
              strengthening.back with
          | none =>
              rw [carrierSuccess] at witnessTypeStrengthens
              cases witnessTypeStrengthens
          | some targetCarrier =>
              cases leftSuccess : leftEndpoint.partialStrengthen?
                  strengthening.back with
              | none =>
                  rw [carrierSuccess, leftSuccess] at witnessTypeStrengthens
                  cases witnessTypeStrengthens
              | some targetLeftEndpoint =>
                  cases rightSuccess : rightEndpoint.partialStrengthen?
                      strengthening.back with
                  | none =>
                      rw [carrierSuccess, leftSuccess, rightSuccess] at witnessTypeStrengthens
                      cases witnessTypeStrengthens
                  | some targetRightEndpoint =>
                      rw [carrierSuccess, leftSuccess, rightSuccess] at witnessTypeStrengthens
                      cases witnessTypeStrengthens
                      exact partialStrengthenTypedIdStrictRecOfSuccess
                        modeIsStrict targetBaseTerm targetWitnessTerm
                        baseTypeStrengthens carrierSuccess leftSuccess
                        rightSuccess baseRawStrengthens witnessRawStrengthens
                        baseTypeRenames baseRawRenames witnessRawRenames

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
    {targetFirstType : Ty level targetScope}
    {targetSecondType : Ty level (targetScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (firstSuccess :
      firstType.partialStrengthen? strengthening.back =
        some targetFirstType)
    (secondSuccess :
      secondType.partialStrengthen? strengthening.back.lift =
        some targetSecondType)
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
    {targetFirstType : Ty level targetScope}
    {targetSecondType : Ty level (targetScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (firstSuccess :
      firstType.partialStrengthen? strengthening.back =
        some targetFirstType)
    (secondSuccess :
      secondType.partialStrengthen? strengthening.back.lift =
        some targetSecondType)
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

/-- Success branch for record-projection strengthening.

Takes the pre-decomposed strengthened field type and the strengthened
record-valued term as explicit witnesses, splitting out the term-mode
body so the strengthening-image soundness layer can prove it without
traversing `Option.casesOn` on the `singleFieldType.partialStrengthen?`
pivot in the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedRecordProjOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {targetFieldType : Ty level targetScope}
    {targetRecordRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (targetRecordTerm :
      Term targetCtx (Ty.record targetFieldType) targetRecordRaw)
    (fieldSuccess :
      singleFieldType.partialStrengthen? strengthening.back =
        some targetFieldType)
    (recordRawStrengthens :
      recordRaw.partialStrengthen? strengthening.back =
        some targetRecordRaw)
    (recordRawRenames :
      recordRaw = targetRecordRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.recordProj recordValue) := {
  targetType := targetFieldType
  targetRaw := RawTerm.recordProj targetRecordRaw
  targetTerm := Term.recordProj targetRecordTerm
  typeStrengthens := fieldSuccess
  rawStrengthens := by
    change
      (match recordRaw.partialStrengthen? strengthening.back with
        | some strengthenedRecord =>
            some (RawTerm.recordProj strengthenedRecord)
        | none => none) =
        some (RawTerm.recordProj targetRecordRaw)
    rw [recordRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename singleFieldType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetFieldType fieldSuccess
  rawRenames := by
    cases recordRawRenames
    rfl
}

/-- Record projection strengthens by strengthening its record payload.

App-pattern: takes the field-type strengthening witness `fieldSuccess`
as an explicit parameter, lifted from the dispatcher's option-split.
The body destructures the record's `StrengtheningResult`, aligns the
`Ty.record` shape via `rw` + `cases` on the derived equation, then
delegates to `partialStrengthenTypedRecordProjOfSuccess`.  This shape
admits a clean App-pattern soundness proof
(`partialStrengthenTypedRecordProj_sound`) by mirror-destructuring +
final-arm `OfSuccess_sound` delegation. -/
def partialStrengthenTypedRecordProj {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {targetFieldType : Ty level targetScope}
    {recordRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (fieldSuccess :
      singleFieldType.partialStrengthen? strengthening.back =
        some targetFieldType)
    (recordResult : StrengtheningResult strengthening recordValue) :
    StrengtheningResult strengthening (Term.recordProj recordValue) := by
  cases recordResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have expectedRecordTypeStrengthens :
          (Ty.record singleFieldType).partialStrengthen? strengthening.back =
            some (Ty.record targetFieldType) := by
        change
          (match singleFieldType.partialStrengthen? strengthening.back with
          | some strengthenedField => some (Ty.record strengthenedField)
          | none => none) =
            some (Ty.record targetFieldType)
        rw [fieldSuccess]
      rw [expectedRecordTypeStrengthens] at typeStrengthens
      cases typeStrengthens
      exact partialStrengthenTypedRecordProjOfSuccess
        targetTerm fieldSuccess rawStrengthens rawRenames

/-- Success branch for codata-unfold strengthening.

Takes pre-decomposed witnesses for the state type, output type, and
both raw component strengthenings.  Splits the term-mode body so the
strengthening-image soundness layer can prove it without traversing
`Eq.casesOn` on the arrow-decomposed transition type strengthening. -/
def partialStrengthenTypedCodataUnfoldOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {targetStateRaw targetTransitionRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (targetStateTerm : Term targetCtx targetStateType targetStateRaw)
    (targetTransitionTerm :
      Term targetCtx (Ty.arrow targetStateType targetOutputType)
        targetTransitionRaw)
    (stateTypeStrengthens :
      stateType.partialStrengthen? strengthening.back = some targetStateType)
    (outputTypeStrengthens :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (stateRawStrengthens :
      stateRaw.partialStrengthen? strengthening.back =
        some targetStateRaw)
    (transitionRawStrengthens :
      transitionRaw.partialStrengthen? strengthening.back =
        some targetTransitionRaw)
    (stateRawRenames :
      stateRaw = targetStateRaw.rename strengthening.forward)
    (transitionRawRenames :
      transitionRaw = targetTransitionRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.codataUnfold initialState transition) := {
  targetType := Ty.codata targetStateType targetOutputType
  targetRaw := RawTerm.codataUnfold targetStateRaw targetTransitionRaw
  targetTerm := Term.codataUnfold targetStateTerm targetTransitionTerm
  typeStrengthens := by
    change
      Option.mapTwo
        (stateType.partialStrengthen? strengthening.back)
        (outputType.partialStrengthen? strengthening.back)
        Ty.codata =
        some (Ty.codata targetStateType targetOutputType)
    rw [stateTypeStrengthens, outputTypeStrengthens]
    rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (stateRaw.partialStrengthen? strengthening.back)
        (transitionRaw.partialStrengthen? strengthening.back)
        RawTerm.codataUnfold =
        some (RawTerm.codataUnfold targetStateRaw targetTransitionRaw)
    rw [stateRawStrengthens, transitionRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename (Ty.codata stateType outputType)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.codata targetStateType targetOutputType)
      (by
        change
          Option.mapTwo
            (stateType.partialStrengthen? strengthening.back)
            (outputType.partialStrengthen? strengthening.back)
            Ty.codata =
            some (Ty.codata targetStateType targetOutputType)
        rw [stateTypeStrengthens, outputTypeStrengthens]
        rfl)
  rawRenames := by
    cases stateRawRenames
    cases transitionRawRenames
    rfl
}

/-- Codata unfold strengthens by strengthening the initial state, the
transition function, and the output type index used by the codata
carrier. -/
def partialStrengthenTypedCodataUnfold {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetOutputType : Ty level targetScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (outputTypeStrengthens :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (stateResult : StrengtheningResult strengthening initialState)
    (transitionResult : StrengtheningResult strengthening transition) :
    StrengtheningResult strengthening
      (Term.codataUnfold initialState transition) := by
  cases stateResult with
  | mk targetStateType targetStateRaw targetStateTerm stateTypeStrengthens
      stateRawStrengthens stateTypeRenames stateRawRenames =>
      cases transitionResult with
      | mk targetTransitionType targetTransitionRaw targetTransitionTerm
          transitionTypeStrengthens transitionRawStrengthens
          transitionTypeRenames transitionRawRenames =>
          change
            Option.mapTwo
              (stateType.partialStrengthen? strengthening.back)
              (outputType.partialStrengthen? strengthening.back)
              Ty.arrow = some targetTransitionType at transitionTypeStrengthens
          rw [stateTypeStrengthens, outputTypeStrengthens]
            at transitionTypeStrengthens
          cases transitionTypeStrengthens
          exact partialStrengthenTypedCodataUnfoldOfSuccess
            targetStateTerm targetTransitionTerm stateTypeStrengthens
            outputTypeStrengthens stateRawStrengthens transitionRawStrengthens
            stateRawRenames transitionRawRenames

/-- Success branch for codata-destruction strengthening.

Takes the pre-decomposed state and output type strengthenings plus the
strengthened codata-valued term as explicit witnesses, splitting the
term-mode body so the soundness layer can prove it without traversing
`Option.casesOn` on the state and output pivots. -/
def partialStrengthenTypedCodataDestOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {codataRaw : RawTerm sourceScope}
    {targetCodataRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (targetCodataTerm :
      Term targetCtx (Ty.codata targetStateType targetOutputType)
        targetCodataRaw)
    (_stateSuccess :
      stateType.partialStrengthen? strengthening.back = some targetStateType)
    (outputSuccess :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (codataRawStrengthens :
      codataRaw.partialStrengthen? strengthening.back =
        some targetCodataRaw)
    (codataRawRenames :
      codataRaw = targetCodataRaw.rename strengthening.forward) :
    StrengtheningResult strengthening (Term.codataDest codataValue) := {
  targetType := targetOutputType
  targetRaw := RawTerm.codataDest targetCodataRaw
  targetTerm := Term.codataDest targetCodataTerm
  typeStrengthens := outputSuccess
  rawStrengthens := by
    change
      (match codataRaw.partialStrengthen? strengthening.back with
        | some strengthenedCodata =>
            some (RawTerm.codataDest strengthenedCodata)
        | none => none) =
        some (RawTerm.codataDest targetCodataRaw)
    rw [codataRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename outputType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetOutputType outputSuccess
  rawRenames := by
    cases codataRawRenames
    rfl
}

/-- Codata destruction strengthens by strengthening the codata payload
and projecting both the state and output strengthenings out of the
codata type index.

App-pattern: takes `stateSuccess` / `outputSuccess` as explicit
parameters lifted from the dispatcher's two option-splits.  The body
destructures the codata value's `StrengtheningResult`, aligns the
`Ty.codata` shape via `rw` + `cases` on the derived equation, then
delegates to `partialStrengthenTypedCodataDestOfSuccess`.  Mirrors the
2-option-split recipe established for RefineElim (Phase 39). -/
def partialStrengthenTypedCodataDest {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {codataRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (stateSuccess :
      stateType.partialStrengthen? strengthening.back = some targetStateType)
    (outputSuccess :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    (codataResult : StrengtheningResult strengthening codataValue) :
    StrengtheningResult strengthening (Term.codataDest codataValue) := by
  cases codataResult with
  | mk targetCodataType targetCodataRaw targetCodataTerm
      codataTypeStrengthens codataRawStrengthens codataTypeRenames
      codataRawRenames =>
      have expectedCodataTypeStrengthens :
          (Ty.codata stateType outputType).partialStrengthen?
              strengthening.back =
            some (Ty.codata targetStateType targetOutputType) := by
        change
          Option.mapTwo
            (stateType.partialStrengthen? strengthening.back)
            (outputType.partialStrengthen? strengthening.back)
            Ty.codata =
              some (Ty.codata targetStateType targetOutputType)
        rw [stateSuccess, outputSuccess]
        rfl
      rw [expectedCodataTypeStrengthens] at codataTypeStrengthens
      cases codataTypeStrengthens
      exact partialStrengthenTypedCodataDestOfSuccess
        targetCodataTerm stateSuccess outputSuccess
        codataRawStrengthens codataRawRenames

/-- Session send strengthens by strengthening the protocol raw, channel,
and payload while preserving the session carrier shape. -/
def partialStrengthenTypedSessionSend {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {targetProtocolStep : RawTerm targetScope}
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (protocolStrengthens :
      protocolStep.partialStrengthen? strengthening.back =
        some targetProtocolStep)
    (channelResult : StrengtheningResult strengthening channel)
    (payloadResult : StrengtheningResult strengthening payload) :
    StrengtheningResult strengthening
      (Term.sessionSend protocolStep channel payload) := by
  cases channelResult with
  | mk targetChannelType targetChannelRaw targetChannelTerm
      channelTypeStrengthens channelRawStrengthens channelTypeRenames
      channelRawRenames =>
      change
        (match protocolStep.partialStrengthen? strengthening.back with
        | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
        | none => none) = some targetChannelType at channelTypeStrengthens
      rw [protocolStrengthens] at channelTypeStrengthens
      cases channelTypeStrengthens
      cases payloadResult with
      | mk targetPayloadType targetPayloadRaw targetPayloadTerm
          payloadTypeStrengthens payloadRawStrengthens payloadTypeRenames
          payloadRawRenames =>
          exact {
            targetType := Ty.session targetProtocolStep
            targetRaw := RawTerm.sessionSend targetChannelRaw targetPayloadRaw
            targetTerm := Term.sessionSend targetProtocolStep
              targetChannelTerm targetPayloadTerm
            typeStrengthens := by
              change
                (match protocolStep.partialStrengthen? strengthening.back with
                | some strengthenedProtocol =>
                    some (Ty.session strengthenedProtocol)
                | none => none) = some (Ty.session targetProtocolStep)
              rw [protocolStrengthens]
            rawStrengthens := by
              change
                Option.mapTwo
                  (channelRaw.partialStrengthen? strengthening.back)
                  (payloadRaw.partialStrengthen? strengthening.back)
                  RawTerm.sessionSend =
                    some (RawTerm.sessionSend targetChannelRaw
                      targetPayloadRaw)
              rw [channelRawStrengthens, payloadRawStrengthens]
              rfl
            typeRenames :=
              Ty.partialStrengthen?_imp_rename (Ty.session protocolStep)
                strengthening.forward strengthening.back
                strengthening.injectsBack (Ty.session targetProtocolStep)
                (by
                  change
                    (match protocolStep.partialStrengthen?
                        strengthening.back with
                    | some strengthenedProtocol =>
                        some (Ty.session strengthenedProtocol)
                    | none => none) = some (Ty.session targetProtocolStep)
                  rw [protocolStrengthens])
            rawRenames := by
              cases channelRawRenames
              cases payloadRawRenames
              rfl
          }

/-- Session receive strengthens by strengthening the channel and
protocol raw while preserving the session carrier shape. -/
def partialStrengthenTypedSessionRecv {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {targetProtocolStep : RawTerm targetScope}
    {channelRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (protocolStrengthens :
      protocolStep.partialStrengthen? strengthening.back =
        some targetProtocolStep)
    (channelResult : StrengtheningResult strengthening channel) :
    StrengtheningResult strengthening (Term.sessionRecv channel) := by
  cases channelResult with
  | mk targetChannelType targetChannelRaw targetChannelTerm
      channelTypeStrengthens channelRawStrengthens channelTypeRenames
      channelRawRenames =>
      change
        (match protocolStep.partialStrengthen? strengthening.back with
        | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
        | none => none) = some targetChannelType at channelTypeStrengthens
      rw [protocolStrengthens] at channelTypeStrengthens
      cases channelTypeStrengthens
      exact {
        targetType := Ty.session targetProtocolStep
        targetRaw := RawTerm.sessionRecv targetChannelRaw
        targetTerm := Term.sessionRecv targetChannelTerm
        typeStrengthens := by
          change
            (match protocolStep.partialStrengthen? strengthening.back with
            | some strengthenedProtocol =>
                some (Ty.session strengthenedProtocol)
            | none => none) = some (Ty.session targetProtocolStep)
          rw [protocolStrengthens]
        rawStrengthens := by
          change
            (match channelRaw.partialStrengthen? strengthening.back with
            | some strengthenedChannel =>
                some (RawTerm.sessionRecv strengthenedChannel)
            | none => none) = some (RawTerm.sessionRecv targetChannelRaw)
          rw [channelRawStrengthens]
        typeRenames :=
          Ty.partialStrengthen?_imp_rename (Ty.session protocolStep)
            strengthening.forward strengthening.back
            strengthening.injectsBack (Ty.session targetProtocolStep)
            (by
              change
                (match protocolStep.partialStrengthen? strengthening.back with
                | some strengthenedProtocol =>
                    some (Ty.session strengthenedProtocol)
                | none => none) = some (Ty.session targetProtocolStep)
              rw [protocolStrengthens])
        rawRenames := congrArg RawTerm.sessionRecv channelRawRenames
      }

/-- Cumulativity promotion strengthens by strengthening its inner
type-code payload and rebuilding the promotion at the target context. -/
def partialStrengthenTypedCumulUp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeResult : StrengtheningResult strengthening typeCode) :
    StrengtheningResult strengthening
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode) := by
  cases codeResult with
  | mk targetCodeType targetCodeRaw targetCodeTerm codeTypeStrengthens
      codeRawStrengthens codeTypeRenames codeRawRenames =>
      cases codeTypeStrengthens
      exact {
        targetType := Ty.universe higherLevel levelLeHigh
        targetRaw := RawTerm.cumulUpMarker targetCodeRaw
        targetTerm := Term.cumulUp lowerLevel higherLevel cumulMonotone
          levelLeLow levelLeHigh targetCodeTerm
        typeStrengthens := rfl
        rawStrengthens := by
          change
            (match codeRaw.partialStrengthen? strengthening.back with
            | some strengthenedCode =>
                some (RawTerm.cumulUpMarker strengthenedCode)
            | none => none) =
              some (RawTerm.cumulUpMarker targetCodeRaw)
          rw [codeRawStrengthens]
        typeRenames := rfl
        rawRenames := congrArg RawTerm.cumulUpMarker codeRawRenames
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

/-- Canonical identity-equivalence terms strengthen by strengthening
their carrier type.  The raw identity functions are binder-local, so
they survive every context strengthening unchanged except for scope. -/
def partialStrengthenTypedEquivReflId {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier) :
    StrengtheningResult strengthening
      (Term.equivReflId (context := sourceCtx) carrier) where
  targetType := Ty.equiv targetCarrier targetCarrier
  targetRaw :=
    RawTerm.equivIntro
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
  targetTerm := Term.equivReflId (context := targetCtx) targetCarrier
  typeStrengthens := by
    change
      Option.mapTwo
        (carrier.partialStrengthen? strengthening.back)
        (carrier.partialStrengthen? strengthening.back)
        Ty.equiv =
          some (Ty.equiv targetCarrier targetCarrier)
    rw [carrierStrengthens]
    rfl
  rawStrengthens := rfl
  typeRenames := by
    rw [Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierStrengthens]
    rfl
  rawRenames := rfl

/-- Canonical universe-identity equivalence witnesses strengthen by
strengthening the represented carrier type and raw universe endpoint.
The proof raw itself is the same binder-local identity equivalence as
`partialStrengthenTypedEquivReflId`. -/
def partialStrengthenTypedEquivReflIdAtId {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierRaw : RawTerm sourceScope)
    (targetCarrierRaw : RawTerm targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (carrierRawStrengthens :
      carrierRaw.partialStrengthen? strengthening.back =
        some targetCarrierRaw) :
    StrengtheningResult strengthening
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel innerLevelLt
        carrier carrierRaw) where
  targetType :=
    Ty.id (Ty.universe innerLevel innerLevelLt)
      targetCarrierRaw targetCarrierRaw
  targetRaw :=
    RawTerm.equivIntro
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
      (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
  targetTerm :=
    by
      have carrierRenames :
          carrier = targetCarrier.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename carrier
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrier carrierStrengthens
      exact Term.equivReflIdAtId (context := targetCtx) innerLevel innerLevelLt
        targetCarrier targetCarrierRaw
  typeStrengthens := by
    change
      Option.mapThree
        ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
          strengthening.back)
        (carrierRaw.partialStrengthen? strengthening.back)
        (carrierRaw.partialStrengthen? strengthening.back)
        Ty.id =
          some (Ty.id (Ty.universe innerLevel innerLevelLt)
            targetCarrierRaw targetCarrierRaw)
    rw [carrierRawStrengthens]
    rfl
  rawStrengthens := rfl
  typeRenames := by
    rw [RawTerm.partialStrengthen?_imp_rename carrierRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierRaw carrierRawStrengthens]
    rfl
  rawRenames := rfl

/-- Canonical funext reflexivity terms strengthen by strengthening the
domain, codomain, and the binder-scoped apply payload. -/
def partialStrengthenTypedFunextRefl {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningResult strengthening
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) where
  targetType :=
    funextReflType targetDomainType targetCodomainType targetApplyRaw
  targetRaw := RawTerm.lam (RawTerm.refl targetApplyRaw)
  targetTerm :=
    Term.funextRefl (context := targetCtx)
      targetDomainType targetCodomainType targetApplyRaw
  typeStrengthens := by
    have codomainWeakenStrengthens :
        codomainType.weaken.partialStrengthen? strengthening.back.lift =
          some targetCodomainType.weaken := by
      rw [Ty.partialStrengthen?_weaken_lift codomainType
        strengthening.back, codomainStrengthens]
      rfl
    have bodyStrengthens :
        (Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
            strengthening.back.lift =
          some (Ty.id targetCodomainType.weaken targetApplyRaw
            targetApplyRaw) := by
      change
        Option.mapThree
          (codomainType.weaken.partialStrengthen? strengthening.back.lift)
          (applyRaw.partialStrengthen? strengthening.back.lift)
          (applyRaw.partialStrengthen? strengthening.back.lift)
          Ty.id =
            some (Ty.id targetCodomainType.weaken targetApplyRaw
              targetApplyRaw)
      rw [codomainWeakenStrengthens, applyStrengthens]
      rfl
    change
      Option.mapTwo
        (domainType.partialStrengthen? strengthening.back)
        ((Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
          strengthening.back.lift)
        Ty.piTy =
          some
            (funextReflType targetDomainType targetCodomainType
              targetApplyRaw)
    rw [domainStrengthens, bodyStrengthens]
    rfl
  rawStrengthens := by
    change RawTerm.partialRename? applyRaw strengthening.back.lift =
      some targetApplyRaw at applyStrengthens
    unfold RawTerm.partialStrengthen? RawTerm.partialRename?
    simp only [RawTerm.partialRename?]
    rw [applyStrengthens]
  typeRenames := by
    exact
      Ty.partialStrengthen?_imp_rename
        (funextReflType domainType codomainType applyRaw)
        strengthening.forward strengthening.back strengthening.injectsBack
        (funextReflType targetDomainType targetCodomainType targetApplyRaw)
        (by
          have codomainWeakenStrengthens :
              codomainType.weaken.partialStrengthen?
                  strengthening.back.lift =
                some targetCodomainType.weaken := by
            rw [Ty.partialStrengthen?_weaken_lift codomainType
              strengthening.back, codomainStrengthens]
            rfl
          have bodyStrengthens :
              (Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
                  strengthening.back.lift =
                some (Ty.id targetCodomainType.weaken targetApplyRaw
                  targetApplyRaw) := by
            change
              Option.mapThree
                (codomainType.weaken.partialStrengthen?
                  strengthening.back.lift)
                (applyRaw.partialStrengthen? strengthening.back.lift)
                (applyRaw.partialStrengthen? strengthening.back.lift)
                Ty.id =
                  some (Ty.id targetCodomainType.weaken targetApplyRaw
                    targetApplyRaw)
            rw [codomainWeakenStrengthens, applyStrengthens]
            rfl
          change
            Option.mapTwo
              (domainType.partialStrengthen? strengthening.back)
              ((Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
                strengthening.back.lift)
              Ty.piTy =
                some
                  (funextReflType targetDomainType targetCodomainType
                    targetApplyRaw)
          rw [domainStrengthens, bodyStrengthens]
          rfl)
  rawRenames := by
    exact
      RawTerm.partialStrengthen?_imp_rename
        (RawTerm.lam (RawTerm.refl applyRaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (RawTerm.lam (RawTerm.refl targetApplyRaw))
        (by
          change RawTerm.partialRename? applyRaw strengthening.back.lift =
            some targetApplyRaw at applyStrengthens
          unfold RawTerm.partialStrengthen? RawTerm.partialRename?
          simp only [RawTerm.partialRename?]
          rw [applyStrengthens])

/-- Id-typed funext reflexivity witnesses use the same strengthened raw
payload as `partialStrengthenTypedFunextRefl`, with a flat arrow
identity carrier. -/
def partialStrengthenTypedFunextReflAtId {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningResult strengthening
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) where
  targetType :=
    Ty.id (Ty.arrow targetDomainType targetCodomainType)
      (RawTerm.lam (RawTerm.refl targetApplyRaw))
      (RawTerm.lam (RawTerm.refl targetApplyRaw))
  targetRaw := RawTerm.lam (RawTerm.refl targetApplyRaw)
  targetTerm :=
    Term.funextReflAtId (context := targetCtx)
      targetDomainType targetCodomainType targetApplyRaw
  typeStrengthens := by
    have arrowStrengthens :
        (Ty.arrow domainType codomainType).partialStrengthen?
            strengthening.back =
          some (Ty.arrow targetDomainType targetCodomainType) := by
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back)
          Ty.arrow =
            some (Ty.arrow targetDomainType targetCodomainType)
      rw [domainStrengthens, codomainStrengthens]
      rfl
    have rawLamStrengthens :
        (RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
            strengthening.back =
          some (RawTerm.lam (RawTerm.refl targetApplyRaw)) := by
      change RawTerm.partialRename? applyRaw strengthening.back.lift =
        some targetApplyRaw at applyStrengthens
      unfold RawTerm.partialStrengthen? RawTerm.partialRename?
      simp only [RawTerm.partialRename?]
      rw [applyStrengthens]
    change
      Option.mapThree
        ((Ty.arrow domainType codomainType).partialStrengthen?
          strengthening.back)
        ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
          strengthening.back)
        ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
          strengthening.back)
        Ty.id =
          some
            (Ty.id (Ty.arrow targetDomainType targetCodomainType)
              (RawTerm.lam (RawTerm.refl targetApplyRaw))
              (RawTerm.lam (RawTerm.refl targetApplyRaw)))
    rw [arrowStrengthens, rawLamStrengthens]
    rfl
  rawStrengthens := by
    change RawTerm.partialRename? applyRaw strengthening.back.lift =
      some targetApplyRaw at applyStrengthens
    unfold RawTerm.partialStrengthen? RawTerm.partialRename?
    simp only [RawTerm.partialRename?]
    rw [applyStrengthens]
  typeRenames := by
    exact
      Ty.partialStrengthen?_imp_rename
        (Ty.id (Ty.arrow domainType codomainType)
          (RawTerm.lam (RawTerm.refl applyRaw))
          (RawTerm.lam (RawTerm.refl applyRaw)))
        strengthening.forward strengthening.back strengthening.injectsBack
        (Ty.id (Ty.arrow targetDomainType targetCodomainType)
          (RawTerm.lam (RawTerm.refl targetApplyRaw))
          (RawTerm.lam (RawTerm.refl targetApplyRaw)))
        (by
          have arrowStrengthens :
              (Ty.arrow domainType codomainType).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetDomainType targetCodomainType) := by
            change
              Option.mapTwo
                (domainType.partialStrengthen? strengthening.back)
                (codomainType.partialStrengthen? strengthening.back)
                Ty.arrow =
                  some (Ty.arrow targetDomainType targetCodomainType)
            rw [domainStrengthens, codomainStrengthens]
            rfl
          have rawLamStrengthens :
              (RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
                  strengthening.back =
                some (RawTerm.lam (RawTerm.refl targetApplyRaw)) := by
            change RawTerm.partialRename? applyRaw strengthening.back.lift =
              some targetApplyRaw at applyStrengthens
            unfold RawTerm.partialStrengthen? RawTerm.partialRename?
            simp only [RawTerm.partialRename?]
            rw [applyStrengthens]
          change
            Option.mapThree
              ((Ty.arrow domainType codomainType).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
                strengthening.back)
              Ty.id =
                some
                  (Ty.id (Ty.arrow targetDomainType targetCodomainType)
                    (RawTerm.lam (RawTerm.refl targetApplyRaw))
                    (RawTerm.lam (RawTerm.refl targetApplyRaw)))
          rw [arrowStrengthens, rawLamStrengthens]
          rfl)
  rawRenames := by
    exact
      RawTerm.partialStrengthen?_imp_rename
        (RawTerm.lam (RawTerm.refl applyRaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (RawTerm.lam (RawTerm.refl targetApplyRaw))
        (by
          change RawTerm.partialRename? applyRaw strengthening.back.lift =
            some targetApplyRaw at applyStrengthens
          unfold RawTerm.partialStrengthen? RawTerm.partialRename?
          simp only [RawTerm.partialRename?]
          rw [applyStrengthens])

/-- Success branch for equivalence-application strengthening.  Mirrors
`partialStrengthenTypedEquivApplyOfSuccess` (Phase 22) but for the
univalence-α companion `Term.equivApp` / `RawTerm.equivApp` constructor
pair.  Same dual Option.casesOn discriminator wall over `Ty.equiv`'s
carrier-pair pivots. -/
def partialStrengthenTypedEquivAppOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw)
    (targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw)
    (_carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.equivApp equivTerm argumentTerm) where
  targetType := targetCarrierB
  targetRaw := RawTerm.equivApp targetEquivRaw targetArgumentRaw
  targetTerm := Term.equivApp targetEquivTerm targetArgumentTerm
  typeStrengthens := carrierBSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (equivRaw.partialStrengthen? strengthening.back)
        (argumentRaw.partialStrengthen? strengthening.back)
        RawTerm.equivApp =
          some (RawTerm.equivApp targetEquivRaw targetArgumentRaw)
    rw [equivRawStrengthens, argumentRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  rawRenames := by
    cases equivRawRenames
    cases argumentRawRenames
    rfl

/-- Equiv-application strengthens by decomposing the strengthened
`Ty.equiv` carrier-pair pivots and threading them into the
`equivApp` constructor at the target context.  Wrapper delegates the
success path to `partialStrengthenTypedEquivAppOfSuccess`. -/
def partialStrengthenTypedEquivApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivResult : StrengtheningResult strengthening equivTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.equivApp equivTerm argumentTerm) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      change
        Option.mapTwo
          (carrierA.partialStrengthen? strengthening.back)
          (carrierB.partialStrengthen? strengthening.back)
          Ty.equiv = some targetEquivType at equivTypeStrengthens
      cases carrierASuccess : carrierA.partialStrengthen?
          strengthening.back with
      | none =>
          rw [carrierASuccess] at equivTypeStrengthens
          cases equivTypeStrengthens
      | some targetCarrierA =>
          cases carrierBSuccess : carrierB.partialStrengthen?
              strengthening.back with
          | none =>
              rw [carrierASuccess, carrierBSuccess] at equivTypeStrengthens
              cases equivTypeStrengthens
          | some targetCarrierB =>
              rw [carrierASuccess, carrierBSuccess] at equivTypeStrengthens
              cases equivTypeStrengthens
              cases argumentResult with
              | mk targetArgumentType targetArgumentRaw targetArgumentTerm
                  argumentTypeStrengthens argumentRawStrengthens
                  argumentTypeRenames argumentRawRenames =>
                  rw [carrierASuccess] at argumentTypeStrengthens
                  cases argumentTypeStrengthens
                  exact partialStrengthenTypedEquivAppOfSuccess
                    targetEquivTerm targetArgumentTerm carrierASuccess
                    carrierBSuccess equivRawStrengthens argumentRawStrengthens
                    equivRawRenames argumentRawRenames

/-- Success branch for equiv-application strengthening.  Takes
pre-decomposed witnesses for the equiv carrier-pair pivots plus the
strengthened equiv-term + argument-term values.  Splits out the
term-mode body so the strengthening-image soundness layer can prove
the soundness theorem without traversing `Option.casesOn` on the
`carrierA.partialStrengthen?` / `carrierB.partialStrengthen?` pivots
inside the wrapper's tactic-mode `cases` chain. -/
def partialStrengthenTypedEquivApplyOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw)
    (targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw)
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.equivApply equivTerm argumentTerm) where
  targetType := targetCarrierB
  targetRaw := RawTerm.equivApply targetEquivRaw targetArgumentRaw
  targetTerm := Term.equivApply targetEquivTerm targetArgumentTerm
  typeStrengthens := carrierBSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (equivRaw.partialStrengthen? strengthening.back)
        (argumentRaw.partialStrengthen? strengthening.back)
        RawTerm.equivApply =
          some (RawTerm.equivApply targetEquivRaw targetArgumentRaw)
    rw [equivRawStrengthens, argumentRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  rawRenames := by
    cases equivRawRenames
    cases argumentRawRenames
    rfl

/-- Univalence-beta equivalence application strengthens with the same
binary proof shape as `partialStrengthenTypedEquivApp`; only the raw
constructor differs.  Wrapper delegates the success path to
`partialStrengthenTypedEquivApplyOfSuccess` so the strengthening-image
soundness layer can skip the wrapper's dual `Option.casesOn`
discriminator wall over `Ty.equiv`'s carrier-pair pivots. -/
def partialStrengthenTypedEquivApply {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivResult : StrengtheningResult strengthening equivTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.equivApply equivTerm argumentTerm) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      change
        Option.mapTwo
          (carrierA.partialStrengthen? strengthening.back)
          (carrierB.partialStrengthen? strengthening.back)
          Ty.equiv = some targetEquivType at equivTypeStrengthens
      cases carrierASuccess : carrierA.partialStrengthen?
          strengthening.back with
      | none =>
          rw [carrierASuccess] at equivTypeStrengthens
          cases equivTypeStrengthens
      | some targetCarrierA =>
          cases carrierBSuccess : carrierB.partialStrengthen?
              strengthening.back with
          | none =>
              rw [carrierASuccess, carrierBSuccess] at equivTypeStrengthens
              cases equivTypeStrengthens
          | some targetCarrierB =>
              rw [carrierASuccess, carrierBSuccess] at equivTypeStrengthens
              cases equivTypeStrengthens
              cases argumentResult with
              | mk targetArgumentType targetArgumentRaw targetArgumentTerm
                  argumentTypeStrengthens argumentRawStrengthens
                  argumentTypeRenames argumentRawRenames =>
                  rw [carrierASuccess] at argumentTypeStrengthens
                  cases argumentTypeStrengthens
                  exact partialStrengthenTypedEquivApplyOfSuccess
                    targetEquivTerm targetArgumentTerm carrierASuccess
                    carrierBSuccess equivRawStrengthens argumentRawStrengthens
                    equivRawRenames argumentRawRenames

/-- `uaToEquiv` strengthens by strengthening its universe-path proof and
the schematic left/right carrier types and raw endpoints. -/
def partialStrengthenTypedUaToEquiv {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (targetLeftTy targetRightTy : Ty level targetScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    (targetLeftTyRaw targetRightTyRaw : RawTerm targetScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw}
    (leftTyStrengthens :
      leftTy.partialStrengthen? strengthening.back = some targetLeftTy)
    (rightTyStrengthens :
      rightTy.partialStrengthen? strengthening.back = some targetRightTy)
    (leftRawStrengthens :
      leftTyRaw.partialStrengthen? strengthening.back = some targetLeftTyRaw)
    (rightRawStrengthens :
      rightTyRaw.partialStrengthen? strengthening.back = some targetRightTyRaw)
    (proofResult : StrengtheningResult strengthening proof) :
    StrengtheningResult strengthening
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm
      proofTypeStrengthens proofRawStrengthens proofTypeRenames
      proofRawRenames =>
      have expectedProofTypeStrengthens :
          (Ty.id (Ty.universe innerLevel innerLevelLt)
              leftTyRaw rightTyRaw).partialStrengthen? strengthening.back =
            some (Ty.id (Ty.universe innerLevel innerLevelLt)
              targetLeftTyRaw targetRightTyRaw) := by
        change
          Option.mapThree
            ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
              strengthening.back)
            (leftTyRaw.partialStrengthen? strengthening.back)
            (rightTyRaw.partialStrengthen? strengthening.back)
            Ty.id =
              some (Ty.id (Ty.universe innerLevel innerLevelLt)
                targetLeftTyRaw targetRightTyRaw)
        rw [leftRawStrengthens, rightRawStrengthens]
        rfl
      rw [expectedProofTypeStrengthens] at proofTypeStrengthens
      cases proofTypeStrengthens
      exact {
        targetType := Ty.equiv targetLeftTy targetRightTy
        targetRaw := RawTerm.uaToEquiv targetProofRaw
        targetTerm :=
          Term.uaToEquiv (context := targetCtx) innerLevel innerLevelLt
            targetLeftTy targetRightTy targetLeftTyRaw targetRightTyRaw
            targetProofTerm
        typeStrengthens := by
          change
            Option.mapTwo
              (leftTy.partialStrengthen? strengthening.back)
              (rightTy.partialStrengthen? strengthening.back)
              Ty.equiv =
                some (Ty.equiv targetLeftTy targetRightTy)
          rw [leftTyStrengthens, rightTyStrengthens]
          rfl
        rawStrengthens := by
          change
            (match proofRaw.partialStrengthen? strengthening.back with
            | some strengthenedProof => some (RawTerm.uaToEquiv strengthenedProof)
            | none => none) =
                some (RawTerm.uaToEquiv targetProofRaw)
          rw [proofRawStrengthens]
        typeRenames := by
          simp only [Ty.rename]
          rw [Ty.partialStrengthen?_imp_rename leftTy
              strengthening.forward strengthening.back
              strengthening.injectsBack targetLeftTy leftTyStrengthens,
            Ty.partialStrengthen?_imp_rename rightTy
              strengthening.forward strengthening.back
              strengthening.injectsBack targetRightTy rightTyStrengthens]
        rawRenames := by
          cases proofRawRenames
          rfl
      }

/-- Observational funext strengthens by strengthening the pointwise
proof plus the schematic domain, codomain, and endpoint raws. -/
def partialStrengthenTypedOeqFunext {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    (targetLeftFunctionRaw targetRightFunctionRaw : RawTerm targetScope)
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (leftFunctionStrengthens :
      leftFunctionRaw.partialStrengthen? strengthening.back =
        some targetLeftFunctionRaw)
    (rightFunctionStrengthens :
      rightFunctionRaw.partialStrengthen? strengthening.back =
        some targetRightFunctionRaw)
    (pointwiseResult : StrengtheningResult strengthening pointwiseProof) :
    StrengtheningResult strengthening
      (Term.oeqFunext (context := sourceCtx) domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof) := by
  cases pointwiseResult with
  | mk targetPointwiseType targetPointwiseRaw targetPointwiseProof
      pointwiseTypeStrengthens pointwiseRawStrengthens
      pointwiseTypeRenames pointwiseRawRenames =>
      have codomainWeakenStrengthens :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift codomainType
          strengthening.back, codomainStrengthens]
        rfl
      have leftWeakenStrengthens :
          leftFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetLeftFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift leftFunctionRaw
          strengthening.back, leftFunctionStrengthens]
        rfl
      have rightWeakenStrengthens :
          rightFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetRightFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift rightFunctionRaw
          strengthening.back, rightFunctionStrengthens]
        rfl
      have pointwiseExpectedStrengthens :
          (oeqFunextPointwiseType domainType codomainType
              leftFunctionRaw rightFunctionRaw).partialStrengthen?
              strengthening.back =
            some (oeqFunextPointwiseType targetDomainType targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw) := by
        have codomainBodyStrengthens :
            (oeqFunextPointwiseCodomain codomainType
                leftFunctionRaw rightFunctionRaw).partialStrengthen?
                strengthening.back.lift =
              some (oeqFunextPointwiseCodomain targetCodomainType
                targetLeftFunctionRaw targetRightFunctionRaw) := by
          have leftAppStrengthens :
              (RawTerm.app leftFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetLeftFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (leftFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetLeftFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [leftWeakenStrengthens]
            rfl
          have rightAppStrengthens :
              (RawTerm.app rightFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetRightFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (rightFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetRightFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [rightWeakenStrengthens]
            rfl
          change
            Option.mapThree
              (codomainType.weaken.partialStrengthen?
                strengthening.back.lift)
              ((RawTerm.app leftFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift)
              ((RawTerm.app rightFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift)
              Ty.oeq =
                some (oeqFunextPointwiseCodomain targetCodomainType
                  targetLeftFunctionRaw targetRightFunctionRaw)
          rw [codomainWeakenStrengthens, leftAppStrengthens,
            rightAppStrengthens]
          rfl
        change
          Option.mapTwo
            (domainType.partialStrengthen? strengthening.back)
            ((oeqFunextPointwiseCodomain codomainType
                leftFunctionRaw rightFunctionRaw).partialStrengthen?
                strengthening.back.lift)
            Ty.piTy =
              some (oeqFunextPointwiseType targetDomainType
                targetCodomainType targetLeftFunctionRaw
                targetRightFunctionRaw)
        rw [domainStrengthens, codomainBodyStrengthens]
        rfl
      rw [pointwiseExpectedStrengthens] at pointwiseTypeStrengthens
      cases pointwiseTypeStrengthens
      exact {
        targetType :=
          Ty.oeq (Ty.arrow targetDomainType targetCodomainType)
            targetLeftFunctionRaw targetRightFunctionRaw
        targetRaw := RawTerm.oeqFunext targetPointwiseRaw
        targetTerm :=
          Term.oeqFunext (context := targetCtx)
            targetDomainType targetCodomainType targetLeftFunctionRaw
            targetRightFunctionRaw targetPointwiseProof
        typeStrengthens := by
          have arrowStrengthens :
              (Ty.arrow domainType codomainType).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetDomainType targetCodomainType) := by
            change
              Option.mapTwo
                (domainType.partialStrengthen? strengthening.back)
                (codomainType.partialStrengthen? strengthening.back)
                Ty.arrow =
                  some (Ty.arrow targetDomainType targetCodomainType)
            rw [domainStrengthens, codomainStrengthens]
            rfl
          change
            Option.mapThree
              ((Ty.arrow domainType codomainType).partialStrengthen?
                strengthening.back)
              (leftFunctionRaw.partialStrengthen? strengthening.back)
              (rightFunctionRaw.partialStrengthen? strengthening.back)
              Ty.oeq =
                some
                  (Ty.oeq (Ty.arrow targetDomainType targetCodomainType)
                    targetLeftFunctionRaw targetRightFunctionRaw)
          rw [arrowStrengthens, leftFunctionStrengthens,
            rightFunctionStrengthens]
          rfl
        rawStrengthens := by
          change
            (match pointwiseRaw.partialStrengthen? strengthening.back with
            | some strengthenedPointwise =>
                some (RawTerm.oeqFunext strengthenedPointwise)
            | none => none) =
              some (RawTerm.oeqFunext targetPointwiseRaw)
          rw [pointwiseRawStrengthens]
        typeRenames := by
          exact
            Ty.partialStrengthen?_imp_rename
              (Ty.oeq (Ty.arrow domainType codomainType)
                leftFunctionRaw rightFunctionRaw)
              strengthening.forward strengthening.back
              strengthening.injectsBack
              (Ty.oeq (Ty.arrow targetDomainType targetCodomainType)
                targetLeftFunctionRaw targetRightFunctionRaw)
              (by
                have arrowStrengthens :
                    (Ty.arrow domainType codomainType).partialStrengthen?
                        strengthening.back =
                      some (Ty.arrow targetDomainType targetCodomainType) := by
                  change
                    Option.mapTwo
                      (domainType.partialStrengthen? strengthening.back)
                      (codomainType.partialStrengthen? strengthening.back)
                      Ty.arrow =
                        some (Ty.arrow targetDomainType targetCodomainType)
                  rw [domainStrengthens, codomainStrengthens]
                  rfl
                change
                  Option.mapThree
                    ((Ty.arrow domainType codomainType).partialStrengthen?
                      strengthening.back)
                    (leftFunctionRaw.partialStrengthen? strengthening.back)
                    (rightFunctionRaw.partialStrengthen? strengthening.back)
                    Ty.oeq =
                      some
                        (Ty.oeq
                          (Ty.arrow targetDomainType targetCodomainType)
                          targetLeftFunctionRaw targetRightFunctionRaw)
                rw [arrowStrengthens, leftFunctionStrengthens,
                  rightFunctionStrengthens]
                rfl)
        rawRenames := by
          cases pointwiseRawRenames
          rfl
      }

/-- Heterogeneous funext-introduction strengthens its flat arrow
identity type and the two binder-scoped apply payloads. -/
def partialStrengthenTypedFunextIntroHet {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1))
    (targetApplyARaw targetApplyBRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyAStrengthens :
      applyARaw.partialStrengthen? strengthening.back.lift =
        some targetApplyARaw)
    (applyBStrengthens :
      applyBRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyBRaw) :
    StrengtheningResult strengthening
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) where
  targetType :=
    Ty.id (Ty.arrow targetDomainType targetCodomainType)
      (RawTerm.lam targetApplyARaw) (RawTerm.lam targetApplyBRaw)
  targetRaw := RawTerm.lam (RawTerm.refl targetApplyARaw)
  targetTerm :=
    Term.funextIntroHet (context := targetCtx)
      targetDomainType targetCodomainType targetApplyARaw targetApplyBRaw
  typeStrengthens := by
    have arrowStrengthens :
        (Ty.arrow domainType codomainType).partialStrengthen?
            strengthening.back =
          some (Ty.arrow targetDomainType targetCodomainType) := by
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back)
          Ty.arrow =
            some (Ty.arrow targetDomainType targetCodomainType)
      rw [domainStrengthens, codomainStrengthens]
      rfl
    have leftLamStrengthens :
        (RawTerm.lam applyARaw).partialStrengthen? strengthening.back =
          some (RawTerm.lam targetApplyARaw) := by
      change RawTerm.partialRename? applyARaw strengthening.back.lift =
        some targetApplyARaw at applyAStrengthens
      unfold RawTerm.partialStrengthen? RawTerm.partialRename?
      rw [applyAStrengthens]
    have rightLamStrengthens :
        (RawTerm.lam applyBRaw).partialStrengthen? strengthening.back =
          some (RawTerm.lam targetApplyBRaw) := by
      change RawTerm.partialRename? applyBRaw strengthening.back.lift =
        some targetApplyBRaw at applyBStrengthens
      unfold RawTerm.partialStrengthen? RawTerm.partialRename?
      rw [applyBStrengthens]
    change
      Option.mapThree
        ((Ty.arrow domainType codomainType).partialStrengthen?
          strengthening.back)
        ((RawTerm.lam applyARaw).partialStrengthen? strengthening.back)
        ((RawTerm.lam applyBRaw).partialStrengthen? strengthening.back)
        Ty.id =
          some
            (Ty.id (Ty.arrow targetDomainType targetCodomainType)
              (RawTerm.lam targetApplyARaw) (RawTerm.lam targetApplyBRaw))
    rw [arrowStrengthens, leftLamStrengthens, rightLamStrengthens]
    rfl
  rawStrengthens := by
    change RawTerm.partialRename? applyARaw strengthening.back.lift =
      some targetApplyARaw at applyAStrengthens
    unfold RawTerm.partialStrengthen? RawTerm.partialRename?
    simp only [RawTerm.partialRename?]
    rw [applyAStrengthens]
  typeRenames := by
    exact
      Ty.partialStrengthen?_imp_rename
        (Ty.id (Ty.arrow domainType codomainType)
          (RawTerm.lam applyARaw) (RawTerm.lam applyBRaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (Ty.id (Ty.arrow targetDomainType targetCodomainType)
          (RawTerm.lam targetApplyARaw) (RawTerm.lam targetApplyBRaw))
        (by
          have arrowStrengthens :
              (Ty.arrow domainType codomainType).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetDomainType targetCodomainType) := by
            change
              Option.mapTwo
                (domainType.partialStrengthen? strengthening.back)
                (codomainType.partialStrengthen? strengthening.back)
                Ty.arrow =
                  some (Ty.arrow targetDomainType targetCodomainType)
            rw [domainStrengthens, codomainStrengthens]
            rfl
          have leftLamStrengthens :
              (RawTerm.lam applyARaw).partialStrengthen?
                  strengthening.back =
                some (RawTerm.lam targetApplyARaw) := by
            change RawTerm.partialRename? applyARaw
              strengthening.back.lift = some targetApplyARaw at applyAStrengthens
            unfold RawTerm.partialStrengthen? RawTerm.partialRename?
            rw [applyAStrengthens]
          have rightLamStrengthens :
              (RawTerm.lam applyBRaw).partialStrengthen?
                  strengthening.back =
                some (RawTerm.lam targetApplyBRaw) := by
            change RawTerm.partialRename? applyBRaw
              strengthening.back.lift = some targetApplyBRaw at applyBStrengthens
            unfold RawTerm.partialStrengthen? RawTerm.partialRename?
            rw [applyBStrengthens]
          change
            Option.mapThree
              ((Ty.arrow domainType codomainType).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam applyARaw).partialStrengthen?
                strengthening.back)
              ((RawTerm.lam applyBRaw).partialStrengthen?
                strengthening.back)
              Ty.id =
                some
                  (Ty.id (Ty.arrow targetDomainType targetCodomainType)
                    (RawTerm.lam targetApplyARaw)
                    (RawTerm.lam targetApplyBRaw))
          rw [arrowStrengthens, leftLamStrengthens, rightLamStrengthens]
          rfl)
  rawRenames := by
    exact
      RawTerm.partialStrengthen?_imp_rename
        (RawTerm.lam (RawTerm.refl applyARaw))
        strengthening.forward strengthening.back strengthening.injectsBack
        (RawTerm.lam (RawTerm.refl targetApplyARaw))
        (by
          change RawTerm.partialRename? applyARaw strengthening.back.lift =
            some targetApplyARaw at applyAStrengthens
          unfold RawTerm.partialStrengthen? RawTerm.partialRename?
          simp only [RawTerm.partialRename?]
          rw [applyAStrengthens])

/-- Heterogeneous univalence introduction strengthens by strengthening
the packaged equivalence witness and the schematic universe endpoints. -/
def partialStrengthenTypedUaIntroHet {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (targetCarrierA targetCarrierB : Ty level targetScope)
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    (targetCarrierARaw targetCarrierBRaw : RawTerm targetScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (targetForwardRaw targetBackwardRaw : RawTerm targetScope)
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (carrierAStrengthens :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBStrengthens :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (carrierARawStrengthens :
      carrierARaw.partialStrengthen? strengthening.back =
        some targetCarrierARaw)
    (carrierBRawStrengthens :
      carrierBRaw.partialStrengthen? strengthening.back =
        some targetCarrierBRaw)
    (forwardRawStrengthens :
      forwardRaw.partialStrengthen? strengthening.back =
        some targetForwardRaw)
    (backwardRawStrengthens :
      backwardRaw.partialStrengthen? strengthening.back =
        some targetBackwardRaw)
    (equivResult : StrengtheningResult strengthening equivWitness) :
    StrengtheningResult strengthening
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivWitness
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv =
              some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierAStrengthens, carrierBStrengthens]
        rfl
      have expectedEquivRawStrengthens :
          (RawTerm.equivIntro forwardRaw backwardRaw).partialStrengthen?
              strengthening.back =
            some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw) := by
        change
          Option.mapTwo
            (forwardRaw.partialStrengthen? strengthening.back)
            (backwardRaw.partialStrengthen? strengthening.back)
            RawTerm.equivIntro =
              some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw)
        rw [forwardRawStrengthens, backwardRawStrengthens]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      rw [expectedEquivRawStrengthens] at equivRawStrengthens
      cases equivTypeStrengthens
      cases equivRawStrengthens
      exact {
        targetType :=
          Ty.id (Ty.universe innerLevel innerLevelLt)
            targetCarrierARaw targetCarrierBRaw
        targetRaw := RawTerm.equivIntro targetForwardRaw targetBackwardRaw
        targetTerm :=
          Term.uaIntroHet (context := targetCtx) innerLevel innerLevelLt
            targetCarrierARaw targetCarrierBRaw targetEquivWitness
        typeStrengthens := by
          change
            Option.mapThree
              ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
                strengthening.back)
              (carrierARaw.partialStrengthen? strengthening.back)
              (carrierBRaw.partialStrengthen? strengthening.back)
              Ty.id =
                some (Ty.id (Ty.universe innerLevel innerLevelLt)
                  targetCarrierARaw targetCarrierBRaw)
          rw [carrierARawStrengthens, carrierBRawStrengthens]
          rfl
        rawStrengthens := expectedEquivRawStrengthens
        typeRenames := by
          exact
            Ty.partialStrengthen?_imp_rename
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                carrierARaw carrierBRaw)
              strengthening.forward strengthening.back
              strengthening.injectsBack
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                targetCarrierARaw targetCarrierBRaw)
              (by
                change
                  Option.mapThree
                    ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
                      strengthening.back)
                    (carrierARaw.partialStrengthen? strengthening.back)
                    (carrierBRaw.partialStrengthen? strengthening.back)
                    Ty.id =
                      some (Ty.id (Ty.universe innerLevel innerLevelLt)
                        targetCarrierARaw targetCarrierBRaw)
                rw [carrierARawStrengthens, carrierBRawStrengthens]
                rfl)
        rawRenames := by
          cases equivRawRenames
          rfl
      }

/-- Glue introduction strengthens by strengthening both payload values
at the same strengthened base type and strengthening the schematic
boundary witness. -/
def partialStrengthenTypedGlueIntro {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (targetBaseType : Ty level targetScope)
    (boundaryWitness : RawTerm sourceScope)
    (targetBoundaryWitness : RawTerm targetScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseTypeStrengthens :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundaryStrengthens :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    (baseResult : StrengtheningResult strengthening baseValue)
    (partialResult : StrengtheningResult strengthening partialValue) :
    StrengtheningResult strengthening
      (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
        boundaryWitness baseValue partialValue) := by
  cases baseResult with
  | mk targetBaseValueType targetBaseRaw targetBaseValue
      baseValueTypeStrengthens baseRawStrengthens baseValueTypeRenames
      baseRawRenames =>
      rw [baseTypeStrengthens] at baseValueTypeStrengthens
      cases baseValueTypeStrengthens
      cases partialResult with
      | mk targetPartialValueType targetPartialRaw targetPartialValue
          partialValueTypeStrengthens partialRawStrengthens
          partialValueTypeRenames partialRawRenames =>
          rw [baseTypeStrengthens] at partialValueTypeStrengthens
          cases partialValueTypeStrengthens
          exact {
            targetType := Ty.glue targetBaseType targetBoundaryWitness
            targetRaw := RawTerm.glueIntro targetBaseRaw targetPartialRaw
            targetTerm :=
              Term.glueIntro (context := targetCtx) modeIsUnivalent
                targetBaseType targetBoundaryWitness targetBaseValue
                targetPartialValue
            typeStrengthens := by
              change
                Option.mapTwo
                  (baseType.partialStrengthen? strengthening.back)
                  (boundaryWitness.partialStrengthen? strengthening.back)
                  Ty.glue =
                    some (Ty.glue targetBaseType targetBoundaryWitness)
              rw [baseTypeStrengthens, boundaryStrengthens]
              rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (baseRaw.partialStrengthen? strengthening.back)
                  (partialRaw.partialStrengthen? strengthening.back)
                  RawTerm.glueIntro =
                    some (RawTerm.glueIntro targetBaseRaw targetPartialRaw)
              rw [baseRawStrengthens, partialRawStrengthens]
              rfl
            typeRenames := by
              exact
                Ty.partialStrengthen?_imp_rename
                  (Ty.glue baseType boundaryWitness)
                  strengthening.forward strengthening.back
                  strengthening.injectsBack
                  (Ty.glue targetBaseType targetBoundaryWitness)
                  (by
                    change
                      Option.mapTwo
                        (baseType.partialStrengthen? strengthening.back)
                        (boundaryWitness.partialStrengthen?
                          strengthening.back)
                        Ty.glue =
                          some (Ty.glue targetBaseType
                            targetBoundaryWitness)
                    rw [baseTypeStrengthens, boundaryStrengthens]
                    rfl)
            rawRenames := by
              cases baseRawRenames
              cases partialRawRenames
              rfl
          }

/-- Success branch for cubical Glue-elimination strengthening.  Takes
pre-decomposed witnesses for the glue carrier's base + boundary pivots
plus the strengthened glued-value.  Splits out the term-mode body so
soundness skips the wrapper's dual `Option.casesOn` discriminator wall
over `Ty.glue`. -/
def partialStrengthenTypedGlueElimOfSuccess {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {targetBaseType : Ty level targetScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {targetBoundaryWitness targetGluedRaw : RawTerm targetScope}
    {gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (targetGluedValue :
      Term targetCtx (Ty.glue targetBaseType targetBoundaryWitness)
        targetGluedRaw)
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (_boundarySuccess :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    (gluedRawStrengthens :
      gluedRaw.partialStrengthen? strengthening.back = some targetGluedRaw)
    (gluedRawRenames :
      gluedRaw = targetGluedRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.glueElim (context := sourceCtx) modeIsUnivalent gluedValue) where
  targetType := targetBaseType
  targetRaw := RawTerm.glueElim targetGluedRaw
  targetTerm := Term.glueElim (context := targetCtx) modeIsUnivalent
    targetGluedValue
  typeStrengthens := baseSuccess
  rawStrengthens := by
    change
      (match gluedRaw.partialStrengthen? strengthening.back with
      | some strengthenedGlued =>
          some (RawTerm.glueElim strengthenedGlued)
      | none => none) =
        some (RawTerm.glueElim targetGluedRaw)
    rw [gluedRawStrengthens]
  typeRenames :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  rawRenames := by
    cases gluedRawRenames
    rfl

/-- Glue elimination strengthens by decomposing the strengthened glue
carrier of the eliminated value.

App-pattern: takes `baseSuccess` and `boundarySuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
base type and boundary witness respectively).  The body destructures
the glued value's `StrengtheningResult`, aligns the `Ty.glue` shape
via `rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedGlueElimOfSuccess`.  Identical 2-option-split
recipe to Phase 39 RefineElim / Phase 40 CodataDest. -/
def partialStrengthenTypedGlueElim {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {targetBaseType : Ty level targetScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {targetBoundaryWitness : RawTerm targetScope}
    {gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundarySuccess :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    (gluedResult : StrengtheningResult strengthening gluedValue) :
    StrengtheningResult strengthening
      (Term.glueElim (context := sourceCtx) modeIsUnivalent gluedValue) := by
  cases gluedResult with
  | mk targetGluedType targetGluedRaw targetGluedValue
      gluedTypeStrengthens gluedRawStrengthens gluedTypeRenames
      gluedRawRenames =>
      have expectedGluedTypeStrengthens :
          (Ty.glue baseType boundaryWitness).partialStrengthen?
              strengthening.back =
            some (Ty.glue targetBaseType targetBoundaryWitness) := by
        change
          Option.mapTwo
            (baseType.partialStrengthen? strengthening.back)
            (boundaryWitness.partialStrengthen? strengthening.back)
            Ty.glue =
              some (Ty.glue targetBaseType targetBoundaryWitness)
        rw [baseSuccess, boundarySuccess]
        rfl
      rw [expectedGluedTypeStrengthens] at gluedTypeStrengthens
      cases gluedTypeStrengthens
      exact partialStrengthenTypedGlueElimOfSuccess
        modeIsUnivalent targetGluedValue baseSuccess
        boundarySuccess gluedRawStrengthens gluedRawRenames

/-- OfSuccess variant of `partialStrengthenTypedTransp` that consumes
pre-witnessed strengthening data for both the typed path and source
children, sparing the soundness proof from replicating the wrapper's
`cases pathResult` / `cases sourceResult` dance.  Reusable from any
caller that has already extracted the typed Path / source witnesses
via separate strengthening lookups (or constructed them directly). -/
def partialStrengthenTypedTranspOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {sourceType targetType : Ty level sourceScope}
    {targetSourceType targetTargetType : Ty level targetScope}
    {sourceTypeRaw targetTypeRaw : RawTerm sourceScope}
    {targetSourceTypeRaw targetTargetTypeRaw : RawTerm targetScope}
    {pathRaw sourceRaw : RawTerm sourceScope}
    {targetPathRaw targetSourceRaw : RawTerm targetScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (targetPath :
      Term targetCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          targetSourceTypeRaw targetTargetTypeRaw)
        targetPathRaw)
    (targetSourceValue :
      Term targetCtx targetSourceType targetSourceRaw)
    (sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (targetTypeRawStrengthens :
      targetTypeRaw.partialStrengthen? strengthening.back =
        some targetTargetTypeRaw)
    (pathRawStrengthens :
      pathRaw.partialStrengthen? strengthening.back =
        some targetPathRaw)
    (sourceRawStrengthens :
      sourceRaw.partialStrengthen? strengthening.back =
        some targetSourceRaw)
    (pathRawRenames :
      pathRaw = targetPathRaw.rename strengthening.forward)
    (sourceRawRenames :
      sourceRaw = targetSourceRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) where
  targetType := targetTargetType
  targetRaw := RawTerm.transp targetPathRaw targetSourceRaw
  targetTerm :=
    Term.transp (context := targetCtx) modeIsUnivalent
      universeLevel universeLevelLt targetSourceType
      targetTargetType targetSourceTypeRaw targetTargetTypeRaw
      targetPath targetSourceValue
  typeStrengthens := targetTypeStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (pathRaw.partialStrengthen? strengthening.back)
        (sourceRaw.partialStrengthen? strengthening.back)
        RawTerm.transp =
          some (RawTerm.transp targetPathRaw targetSourceRaw)
    rw [pathRawStrengthens, sourceRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename targetType
      strengthening.forward strengthening.back
      strengthening.injectsBack targetTargetType
      targetTypeStrengthens
  rawRenames := by
    cases pathRawRenames
    cases sourceRawRenames
    rfl

/-- Cubical transport strengthens by strengthening the path proof, the
source value, and the schematic source/target carrier data. -/
def partialStrengthenTypedTransp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (targetSourceType targetTargetType : Ty level targetScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    (targetSourceTypeRaw targetTargetTypeRaw : RawTerm targetScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (targetTypeRawStrengthens :
      targetTypeRaw.partialStrengthen? strengthening.back =
        some targetTargetTypeRaw)
    (pathResult : StrengtheningResult strengthening typePath)
    (sourceResult : StrengtheningResult strengthening sourceValue) :
    StrengtheningResult strengthening
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPath
      pathTypeStrengthens pathRawStrengthens pathTypeRenames pathRawRenames =>
      have expectedPathTypeStrengthens :
          (Ty.path (Ty.universe universeLevel universeLevelLt)
              sourceTypeRaw targetTypeRaw).partialStrengthen?
              strengthening.back =
            some (Ty.path (Ty.universe universeLevel universeLevelLt)
              targetSourceTypeRaw targetTargetTypeRaw) := by
        change
          Option.mapThree
            ((Ty.universe universeLevel universeLevelLt).partialStrengthen?
              strengthening.back)
            (sourceTypeRaw.partialStrengthen? strengthening.back)
            (targetTypeRaw.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path (Ty.universe universeLevel universeLevelLt)
                targetSourceTypeRaw targetTargetTypeRaw)
        rw [sourceTypeRawStrengthens, targetTypeRawStrengthens]
        rfl
      rw [expectedPathTypeStrengthens] at pathTypeStrengthens
      cases pathTypeStrengthens
      cases sourceResult with
      | mk targetSourceValueType targetSourceRaw targetSourceValue
          sourceValueTypeStrengthens sourceRawStrengthens
          sourceValueTypeRenames sourceRawRenames =>
          rw [sourceTypeStrengthens] at sourceValueTypeStrengthens
          cases sourceValueTypeStrengthens
          exact {
            targetType := targetTargetType
            targetRaw := RawTerm.transp targetPathRaw targetSourceRaw
            targetTerm :=
              Term.transp (context := targetCtx) modeIsUnivalent
                universeLevel universeLevelLt targetSourceType
                targetTargetType targetSourceTypeRaw targetTargetTypeRaw
                targetPath targetSourceValue
            typeStrengthens := targetTypeStrengthens
            rawStrengthens := by
              change
                Option.mapTwo
                  (pathRaw.partialStrengthen? strengthening.back)
                  (sourceRaw.partialStrengthen? strengthening.back)
                  RawTerm.transp =
                    some (RawTerm.transp targetPathRaw targetSourceRaw)
              rw [pathRawStrengthens, sourceRawStrengthens]
              rfl
            typeRenames :=
              Ty.partialStrengthen?_imp_rename targetType
                strengthening.forward strengthening.back
                strengthening.injectsBack targetTargetType
                targetTypeStrengthens
            rawRenames := by
              cases pathRawRenames
              cases sourceRawRenames
              rfl
          }

/-- OfSuccess variant of `partialStrengthenTypedHcomp` consuming
pre-witnessed strengthening data for both typed children, sparing the
soundness proof from the wrapper's nested `cases sidesResult` /
`cases capResult` dance. -/
def partialStrengthenTypedHcompOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {targetSidesRaw targetCapRaw : RawTerm targetScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (targetSidesValue :
      Term targetCtx targetCarrierType targetSidesRaw)
    (targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw)
    (carrierStrengthens :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (sidesRawStrengthens :
      sidesRaw.partialStrengthen? strengthening.back =
        some targetSidesRaw)
    (capRawStrengthens :
      capRaw.partialStrengthen? strengthening.back =
        some targetCapRaw)
    (sidesRawRenames :
      sidesRaw = targetSidesRaw.rename strengthening.forward)
    (capRawRenames :
      capRaw = targetCapRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.hcomp (context := sourceCtx) modeIsUnivalent sidesValue
        capValue) where
  targetType := targetCarrierType
  targetRaw := RawTerm.hcomp targetSidesRaw targetCapRaw
  targetTerm :=
    Term.hcomp (context := targetCtx) modeIsUnivalent
      targetSidesValue targetCapValue
  typeStrengthens := carrierStrengthens
  rawStrengthens := by
    change
      Option.mapTwo
        (sidesRaw.partialStrengthen? strengthening.back)
        (capRaw.partialStrengthen? strengthening.back)
        RawTerm.hcomp =
          some (RawTerm.hcomp targetSidesRaw targetCapRaw)
    rw [sidesRawStrengthens, capRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back
      strengthening.injectsBack targetCarrierType
      carrierStrengthens
  rawRenames := by
    cases sidesRawRenames
    cases capRawRenames
    rfl

/-- Homogeneous composition strengthens by strengthening both carrier
payloads at the same strengthened carrier type. -/
def partialStrengthenTypedHcomp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesResult : StrengtheningResult strengthening sidesValue)
    (capResult : StrengtheningResult strengthening capValue) :
    StrengtheningResult strengthening
      (Term.hcomp (context := sourceCtx) modeIsUnivalent sidesValue
        capValue) := by
  cases sidesResult with
  | mk targetCarrierType targetSidesRaw targetSidesValue
      carrierStrengthens sidesRawStrengthens carrierRenames
      sidesRawRenames =>
      cases capResult with
      | mk targetCapType targetCapRaw targetCapValue capTypeStrengthens
          capRawStrengthens capTypeRenames capRawRenames =>
          rw [carrierStrengthens] at capTypeStrengthens
          cases capTypeStrengthens
          exact {
            targetType := targetCarrierType
            targetRaw := RawTerm.hcomp targetSidesRaw targetCapRaw
            targetTerm :=
              Term.hcomp (context := targetCtx) modeIsUnivalent
                targetSidesValue targetCapValue
            typeStrengthens := carrierStrengthens
            rawStrengthens := by
              change
                Option.mapTwo
                  (sidesRaw.partialStrengthen? strengthening.back)
                  (capRaw.partialStrengthen? strengthening.back)
                  RawTerm.hcomp =
                    some (RawTerm.hcomp targetSidesRaw targetCapRaw)
              rw [sidesRawStrengthens, capRawStrengthens]
              rfl
            typeRenames := carrierRenames
            rawRenames := by
              cases sidesRawRenames
              cases capRawRenames
              rfl
          }

/-- Pre-witnessed path-shaped homogeneous composition strengthening.

Replaces the wrapper's nested `Option.casesOn` on `Ty.path`'s
carrier + leftEndpoint + rightEndpoint pivots with explicit
strengthening witnesses for each.  The unused
`_leftSuccess`/`_rightSuccess` are kept in the signature so the
OfSuccess-sound theorem can recover the endpoint renaming
equalities used by `hcompPath_HEq_congr`. -/
def partialStrengthenTypedHcompPathOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {targetSidesPathRaw targetCapRaw : RawTerm targetScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (targetSidesPath :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetSidesPathRaw)
    (targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw)
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (_leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (_rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (sidesPathRawStrengthens :
      sidesPathRaw.partialStrengthen? strengthening.back =
        some targetSidesPathRaw)
    (capRawStrengthens :
      capRaw.partialStrengthen? strengthening.back =
        some targetCapRaw)
    (sidesPathRawRenames :
      sidesPathRaw = targetSidesPathRaw.rename strengthening.forward)
    (capRawRenames :
      capRaw = targetCapRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.hcompPath (context := sourceCtx) modeIsUnivalent
        leftEndpoint rightEndpoint sidesPath capValue) where
  targetType := targetCarrierType
  targetRaw := RawTerm.hcomp targetSidesPathRaw targetCapRaw
  targetTerm :=
    Term.hcompPath (context := targetCtx) modeIsUnivalent
      targetLeftEndpoint targetRightEndpoint targetSidesPath
      targetCapValue
  typeStrengthens := carrierSuccess
  rawStrengthens := by
    change
      Option.mapTwo
        (sidesPathRaw.partialStrengthen? strengthening.back)
        (capRaw.partialStrengthen? strengthening.back)
        RawTerm.hcomp =
          some (RawTerm.hcomp targetSidesPathRaw targetCapRaw)
    rw [sidesPathRawStrengthens, capRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back
      strengthening.injectsBack targetCarrierType carrierSuccess
  rawRenames := by
    cases sidesPathRawRenames
    cases capRawRenames
    rfl

/-- Path-shaped homogeneous composition strengthens by decomposing the
strengthened path carrier for the sides and aligning the cap carrier. -/
def partialStrengthenTypedHcompPath {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesPathResult : StrengtheningResult strengthening sidesPath)
    (capResult : StrengtheningResult strengthening capValue) :
    StrengtheningResult strengthening
      (Term.hcompPath (context := sourceCtx) modeIsUnivalent
        leftEndpoint rightEndpoint sidesPath capValue) := by
  cases sidesPathResult with
  | mk targetSidesPathType targetSidesPathRaw targetSidesPath
      sidesPathTypeStrengthens sidesPathRawStrengthens
      sidesPathTypeRenames sidesPathRawRenames =>
      change
        Option.mapThree
          (carrierType.partialStrengthen? strengthening.back)
          (leftEndpoint.partialStrengthen? strengthening.back)
          (rightEndpoint.partialStrengthen? strengthening.back)
          Ty.path = some targetSidesPathType at sidesPathTypeStrengthens
      cases carrierSuccess : carrierType.partialStrengthen?
          strengthening.back with
      | none =>
          rw [carrierSuccess] at sidesPathTypeStrengthens
          cases sidesPathTypeStrengthens
      | some targetCarrierType =>
          cases leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none =>
              rw [carrierSuccess, leftSuccess] at sidesPathTypeStrengthens
              cases sidesPathTypeStrengthens
          | some targetLeftEndpoint =>
              cases rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none =>
                  rw [carrierSuccess, leftSuccess, rightSuccess] at sidesPathTypeStrengthens
                  cases sidesPathTypeStrengthens
              | some targetRightEndpoint =>
                  rw [carrierSuccess, leftSuccess, rightSuccess] at sidesPathTypeStrengthens
                  cases sidesPathTypeStrengthens
                  cases capResult with
                  | mk targetCapType targetCapRaw targetCapValue
                      capTypeStrengthens capRawStrengthens capTypeRenames
                      capRawRenames =>
                      rw [carrierSuccess] at capTypeStrengthens
                      cases capTypeStrengthens
                      exact {
                        targetType := targetCarrierType
                        targetRaw :=
                          RawTerm.hcomp targetSidesPathRaw targetCapRaw
                        targetTerm :=
                          Term.hcompPath (context := targetCtx)
                            modeIsUnivalent targetLeftEndpoint
                            targetRightEndpoint targetSidesPath
                            targetCapValue
                        typeStrengthens := carrierSuccess
                        rawStrengthens := by
                          change
                            Option.mapTwo
                              (sidesPathRaw.partialStrengthen?
                                strengthening.back)
                              (capRaw.partialStrengthen? strengthening.back)
                              RawTerm.hcomp =
                                some (RawTerm.hcomp targetSidesPathRaw
                                  targetCapRaw)
                          rw [sidesPathRawStrengthens, capRawStrengthens]
                          rfl
                        typeRenames :=
                          Ty.partialStrengthen?_imp_rename carrierType
                            strengthening.forward strengthening.back
                            strengthening.injectsBack targetCarrierType
                            carrierSuccess
                        rawRenames := by
                          cases sidesPathRawRenames
                          cases capRawRenames
                          rfl
                      }

/-- Pre-witnessed effect-performance strengthening.

Replaces the wrapper's nested `cases operationTagResult` and
`cases argumentsResult` plus their `expectedOperationTagTypeStrengthens`
rewrites with explicit strengthening witnesses for both raw operands.
The `targetCanPerform` evidence is built structurally via
`CanPerform.map`-style dispatch on `canPerformOperation`, and the
target operation-signature carries the same `effectLabel` so its
`map`-renamed form composes definitionally with the source signature
after carrier renames are recovered. -/
def partialStrengthenTypedEffectPerformOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {effectTag : RawTerm sourceScope}
    {targetEffectTag : RawTerm targetScope}
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    {targetArgumentCarrier targetResultCarrier : Ty level targetScope}
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {targetOperationRaw targetArgumentsRaw : RawTerm targetScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (targetOperationTag :
      Term targetCtx
        (Ty.effect targetArgumentCarrier targetEffectTag)
        targetOperationRaw)
    (targetArguments :
      Term targetCtx targetArgumentCarrier targetArgumentsRaw)
    (effectTagStrengthens :
      effectTag.partialStrengthen? strengthening.back =
        some targetEffectTag)
    (argumentCarrierStrengthens :
      operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back =
        some targetArgumentCarrier)
    (resultCarrierStrengthens :
      operationSignature.resultCarrier.partialStrengthen?
          strengthening.back =
        some targetResultCarrier)
    (operationRawStrengthens :
      operationRaw.partialStrengthen? strengthening.back =
        some targetOperationRaw)
    (argumentsRawStrengthens :
      argumentsRaw.partialStrengthen? strengthening.back =
        some targetArgumentsRaw)
    (effectTagRenames :
      effectTag = targetEffectTag.rename strengthening.forward)
    (operationRawRenames :
      operationRaw = targetOperationRaw.rename strengthening.forward)
    (argumentsRawRenames :
      argumentsRaw = targetArgumentsRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  let targetOperationSignature : Effects.OperationSignature
      (Ty level targetScope) :=
    { effectLabel := operationSignature.effectLabel
      argumentCarrier := targetArgumentCarrier
      resultCarrier := targetResultCarrier }
  have targetCanPerform :
      Effects.CanPerform effectRow targetOperationSignature := by
    cases canPerformOperation with
    | direct rowMember =>
        exact Effects.CanPerform.direct rowMember
    | readViaWrite argumentCarrier resultCarrier rowMember =>
        exact Effects.CanPerform.readViaWrite targetArgumentCarrier
          targetResultCarrier rowMember
  exact {
    targetType := Ty.effect targetResultCarrier targetEffectTag
    targetRaw :=
      RawTerm.effectPerform targetOperationRaw targetArgumentsRaw
    targetTerm :=
      Term.effectPerform (context := targetCtx) targetEffectTag
        effectRow targetOperationSignature targetCanPerform
        targetOperationTag targetArguments
    typeStrengthens := by
      change
        Option.mapTwo
          (operationSignature.resultCarrier.partialStrengthen?
            strengthening.back)
          (effectTag.partialStrengthen? strengthening.back)
          Ty.effect =
            some (Ty.effect targetResultCarrier targetEffectTag)
      rw [resultCarrierStrengthens, effectTagStrengthens]
      rfl
    rawStrengthens := by
      change
        Option.mapTwo
          (operationRaw.partialStrengthen? strengthening.back)
          (argumentsRaw.partialStrengthen? strengthening.back)
          RawTerm.effectPerform =
            some (RawTerm.effectPerform targetOperationRaw
              targetArgumentsRaw)
      rw [operationRawStrengthens, argumentsRawStrengthens]
      rfl
    typeRenames :=
      Ty.partialStrengthen?_imp_rename
        (Ty.effect operationSignature.resultCarrier effectTag)
        strengthening.forward strengthening.back
        strengthening.injectsBack
        (Ty.effect targetResultCarrier targetEffectTag)
        (by
          change
            Option.mapTwo
              (operationSignature.resultCarrier.partialStrengthen?
                strengthening.back)
              (effectTag.partialStrengthen? strengthening.back)
              Ty.effect =
                some (Ty.effect targetResultCarrier targetEffectTag)
          rw [resultCarrierStrengthens, effectTagStrengthens]
          rfl)
    rawRenames := by
      cases operationRawRenames
      cases argumentsRawRenames
      rfl
  }

/-- Effect performance strengthens by strengthening the operation tag,
argument term, effect tag, and the operation signature's argument/result
carriers.  `CanPerform` evidence is rebuilt structurally because it
depends only on the effect label and row membership, not on carrier
internals. -/
def partialStrengthenTypedEffectPerform {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (effectTag : RawTerm sourceScope)
    (targetEffectTag : RawTerm targetScope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (targetArgumentCarrier targetResultCarrier : Ty level targetScope)
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (effectTagStrengthens :
      effectTag.partialStrengthen? strengthening.back =
        some targetEffectTag)
    (argumentCarrierStrengthens :
      operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back =
        some targetArgumentCarrier)
    (resultCarrierStrengthens :
      operationSignature.resultCarrier.partialStrengthen?
          strengthening.back =
        some targetResultCarrier)
    (operationTagResult : StrengtheningResult strengthening operationTag)
    (argumentsResult : StrengtheningResult strengthening arguments) :
    StrengtheningResult strengthening
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  let targetOperationSignature : Effects.OperationSignature
      (Ty level targetScope) :=
    { effectLabel := operationSignature.effectLabel
      argumentCarrier := targetArgumentCarrier
      resultCarrier := targetResultCarrier }
  have targetCanPerform :
      Effects.CanPerform effectRow targetOperationSignature := by
    cases canPerformOperation with
    | direct rowMember =>
        exact Effects.CanPerform.direct rowMember
    | readViaWrite argumentCarrier resultCarrier rowMember =>
        exact Effects.CanPerform.readViaWrite targetArgumentCarrier
          targetResultCarrier rowMember
  cases operationTagResult with
  | mk targetOperationTagType targetOperationRaw targetOperationTag
      operationTagTypeStrengthens operationRawStrengthens
      operationTagTypeRenames operationRawRenames =>
      have expectedOperationTagTypeStrengthens :
          (Ty.effect operationSignature.argumentCarrier effectTag).partialStrengthen?
              strengthening.back =
            some (Ty.effect targetArgumentCarrier targetEffectTag) := by
        change
          Option.mapTwo
            (operationSignature.argumentCarrier.partialStrengthen?
              strengthening.back)
            (effectTag.partialStrengthen? strengthening.back)
            Ty.effect =
              some (Ty.effect targetArgumentCarrier targetEffectTag)
        rw [argumentCarrierStrengthens, effectTagStrengthens]
        rfl
      rw [expectedOperationTagTypeStrengthens] at operationTagTypeStrengthens
      cases operationTagTypeStrengthens
      cases argumentsResult with
      | mk targetArgumentsType targetArgumentsRaw targetArguments
          argumentsTypeStrengthens argumentsRawStrengthens
          argumentsTypeRenames argumentsRawRenames =>
          rw [argumentCarrierStrengthens] at argumentsTypeStrengthens
          cases argumentsTypeStrengthens
          exact {
            targetType := Ty.effect targetResultCarrier targetEffectTag
            targetRaw :=
              RawTerm.effectPerform targetOperationRaw targetArgumentsRaw
            targetTerm :=
              Term.effectPerform (context := targetCtx) targetEffectTag
                effectRow targetOperationSignature targetCanPerform
                targetOperationTag targetArguments
            typeStrengthens := by
              change
                Option.mapTwo
                  (operationSignature.resultCarrier.partialStrengthen?
                    strengthening.back)
                  (effectTag.partialStrengthen? strengthening.back)
                  Ty.effect =
                    some (Ty.effect targetResultCarrier targetEffectTag)
              rw [resultCarrierStrengthens, effectTagStrengthens]
              rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (operationRaw.partialStrengthen? strengthening.back)
                  (argumentsRaw.partialStrengthen? strengthening.back)
                  RawTerm.effectPerform =
                    some (RawTerm.effectPerform targetOperationRaw
                      targetArgumentsRaw)
              rw [operationRawStrengthens, argumentsRawStrengthens]
              rfl
            typeRenames := by
              exact
                Ty.partialStrengthen?_imp_rename
                  (Ty.effect operationSignature.resultCarrier effectTag)
                  strengthening.forward strengthening.back
                  strengthening.injectsBack
                  (Ty.effect targetResultCarrier targetEffectTag)
                  (by
                    change
                      Option.mapTwo
                        (operationSignature.resultCarrier.partialStrengthen?
                          strengthening.back)
                        (effectTag.partialStrengthen? strengthening.back)
                        Ty.effect =
                          some (Ty.effect targetResultCarrier
                            targetEffectTag)
                    rw [resultCarrierStrengthens, effectTagStrengthens]
                    rfl)
            rawRenames := by
              cases operationRawRenames
              cases argumentsRawRenames
              rfl
          }

/-- Pre-witnessed heterogeneous equivalence introduction
strengthening.  Replaces the wrapper's deep `Option.casesOn` cascade
over `Ty.arrow`'s two pivots plus the four nested
`equivIntroHet*InverseType` derivations with explicit strengthening
witnesses for both carriers and both raw operand terms.  The four
typed children (forward / backward / leftInv / rightInv) and their
target counterparts are passed directly; `targetLeftInvRaw` /
`targetRightInvRaw` are implicit since `RawTerm.equivIntro`'s
schematic raw form only references `forwardRaw` / `backwardRaw`. -/
def partialStrengthenTypedEquivIntroHetOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {targetForwardRaw targetBackwardRaw : RawTerm targetScope}
    {targetLeftInvRaw targetRightInvRaw : RawTerm targetScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (targetForward :
      Term targetCtx (Ty.arrow targetCarrierA targetCarrierB)
        targetForwardRaw)
    (targetBackward :
      Term targetCtx (Ty.arrow targetCarrierB targetCarrierA)
        targetBackwardRaw)
    (targetLeftInv :
      Term targetCtx
        (equivIntroHetLeftInverseType targetCarrierA targetForwardRaw
          targetBackwardRaw)
        targetLeftInvRaw)
    (targetRightInv :
      Term targetCtx
        (equivIntroHetRightInverseType targetCarrierB targetForwardRaw
          targetBackwardRaw)
        targetRightInvRaw)
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back =
        some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back =
        some targetCarrierB)
    (forwardRawStrengthens :
      forwardRaw.partialStrengthen? strengthening.back =
        some targetForwardRaw)
    (backwardRawStrengthens :
      backwardRaw.partialStrengthen? strengthening.back =
        some targetBackwardRaw)
    (forwardRawRenames :
      forwardRaw = targetForwardRaw.rename strengthening.forward)
    (backwardRawRenames :
      backwardRaw = targetBackwardRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.equivIntroHet forward backward leftInv rightInv) where
  targetType := Ty.equiv targetCarrierA targetCarrierB
  targetRaw := RawTerm.equivIntro targetForwardRaw targetBackwardRaw
  targetTerm :=
    Term.equivIntroHet targetForward targetBackward targetLeftInv
      targetRightInv
  typeStrengthens := by
    change
      Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv =
          some (Ty.equiv targetCarrierA targetCarrierB)
    rw [carrierASuccess, carrierBSuccess]
    rfl
  rawStrengthens := by
    change
      Option.mapTwo
        (forwardRaw.partialStrengthen? strengthening.back)
        (backwardRaw.partialStrengthen? strengthening.back)
        RawTerm.equivIntro =
          some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw)
    rw [forwardRawStrengthens, backwardRawStrengthens]
    rfl
  typeRenames :=
    Ty.partialStrengthen?_imp_rename (Ty.equiv carrierA carrierB)
      strengthening.forward strengthening.back strengthening.injectsBack
      (Ty.equiv targetCarrierA targetCarrierB)
      (by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv =
              some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl)
  rawRenames := by
    cases forwardRawRenames
    cases backwardRawRenames
    rfl

/-- Heterogeneous equivalence introduction strengthens the forward and
backward functions plus their inverse-law proof functions.  The proof
children are aligned by structurally strengthening the named inverse-law
types from `TermHelpers`. -/
def partialStrengthenTypedEquivIntroHet {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardResult : StrengtheningResult strengthening forward)
    (backwardResult : StrengtheningResult strengthening backward)
    (leftInvResult : StrengtheningResult strengthening leftInv)
    (rightInvResult : StrengtheningResult strengthening rightInv) :
    StrengtheningResult strengthening
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  cases forwardResult with
  | mk targetForwardType targetForwardRaw targetForward
      forwardTypeStrengthens forwardRawStrengthens forwardTypeRenames
      forwardRawRenames =>
      change
        Option.mapTwo
          (carrierA.partialStrengthen? strengthening.back)
          (carrierB.partialStrengthen? strengthening.back)
          Ty.arrow = some targetForwardType at forwardTypeStrengthens
      cases carrierASuccess : carrierA.partialStrengthen?
          strengthening.back with
      | none =>
          rw [carrierASuccess] at forwardTypeStrengthens
          cases forwardTypeStrengthens
      | some targetCarrierA =>
          cases carrierBSuccess : carrierB.partialStrengthen?
              strengthening.back with
          | none =>
              rw [carrierASuccess, carrierBSuccess] at forwardTypeStrengthens
              cases forwardTypeStrengthens
          | some targetCarrierB =>
              rw [carrierASuccess, carrierBSuccess] at forwardTypeStrengthens
              cases forwardTypeStrengthens
              cases backwardResult with
              | mk targetBackwardType targetBackwardRaw targetBackward
                  backwardTypeStrengthens backwardRawStrengthens
                  backwardTypeRenames backwardRawRenames =>
                  have expectedBackwardTypeStrengthens :
                      (Ty.arrow carrierB carrierA).partialStrengthen?
                          strengthening.back =
                        some (Ty.arrow targetCarrierB targetCarrierA) := by
                    change
                      Option.mapTwo
                        (carrierB.partialStrengthen? strengthening.back)
                        (carrierA.partialStrengthen? strengthening.back)
                        Ty.arrow =
                          some (Ty.arrow targetCarrierB targetCarrierA)
                    rw [carrierBSuccess, carrierASuccess]
                    rfl
                  rw [expectedBackwardTypeStrengthens] at backwardTypeStrengthens
                  cases backwardTypeStrengthens
                  have forwardWeakenStrengthens :
                      forwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetForwardRaw.weaken := by
                    rw [RawTerm.partialStrengthen?_weaken_lift forwardRaw
                      strengthening.back, forwardRawStrengthens]
                    rfl
                  have backwardWeakenStrengthens :
                      backwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetBackwardRaw.weaken := by
                    rw [RawTerm.partialStrengthen?_weaken_lift backwardRaw
                      strengthening.back, backwardRawStrengthens]
                    rfl
                  have carrierAWeakenStrengthens :
                      carrierA.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetCarrierA.weaken := by
                    rw [Ty.partialStrengthen?_weaken_lift carrierA
                      strengthening.back, carrierASuccess]
                    rfl
                  have carrierBWeakenStrengthens :
                      carrierB.weaken.partialStrengthen?
                          strengthening.back.lift =
                        some targetCarrierB.weaken := by
                    rw [Ty.partialStrengthen?_weaken_lift carrierB
                      strengthening.back, carrierBSuccess]
                    rfl
                  have forwardVarAppStrengthens :
                      (RawTerm.app forwardRaw.weaken
                        (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                        ).partialStrengthen? strengthening.back.lift =
                        some (RawTerm.app targetForwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
                    change
                      Option.mapTwo
                        (forwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        (some (RawTerm.var
                          ⟨0, Nat.zero_lt_succ targetScope⟩))
                        RawTerm.app =
                          some (RawTerm.app targetForwardRaw.weaken
                            (RawTerm.var
                              ⟨0, Nat.zero_lt_succ targetScope⟩))
                    rw [forwardWeakenStrengthens]
                    rfl
                  have backwardVarAppStrengthens :
                      (RawTerm.app backwardRaw.weaken
                        (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                        ).partialStrengthen? strengthening.back.lift =
                        some (RawTerm.app targetBackwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
                    change
                      Option.mapTwo
                        (backwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        (some (RawTerm.var
                          ⟨0, Nat.zero_lt_succ targetScope⟩))
                        RawTerm.app =
                          some (RawTerm.app targetBackwardRaw.weaken
                            (RawTerm.var
                              ⟨0, Nat.zero_lt_succ targetScope⟩))
                    rw [backwardWeakenStrengthens]
                    rfl
                  have leftNestedAppStrengthens :
                      (RawTerm.app backwardRaw.weaken
                        (RawTerm.app forwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
                        ).partialStrengthen? strengthening.back.lift =
                        some
                          (RawTerm.app targetBackwardRaw.weaken
                            (RawTerm.app targetForwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ targetScope⟩))) := by
                    change
                      Option.mapTwo
                        (backwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        ((RawTerm.app forwardRaw.weaken
                          (RawTerm.var
                            ⟨0, Nat.zero_lt_succ sourceScope⟩)
                          ).partialStrengthen? strengthening.back.lift)
                        RawTerm.app =
                          some
                            (RawTerm.app targetBackwardRaw.weaken
                              (RawTerm.app targetForwardRaw.weaken
                                (RawTerm.var
                                  ⟨0, Nat.zero_lt_succ targetScope⟩)))
                    rw [backwardWeakenStrengthens, forwardVarAppStrengthens]
                    rfl
                  have rightNestedAppStrengthens :
                      (RawTerm.app forwardRaw.weaken
                        (RawTerm.app backwardRaw.weaken
                          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
                        ).partialStrengthen? strengthening.back.lift =
                        some
                          (RawTerm.app targetForwardRaw.weaken
                            (RawTerm.app targetBackwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ targetScope⟩))) := by
                    change
                      Option.mapTwo
                        (forwardRaw.weaken.partialStrengthen?
                          strengthening.back.lift)
                        ((RawTerm.app backwardRaw.weaken
                          (RawTerm.var
                            ⟨0, Nat.zero_lt_succ sourceScope⟩)
                          ).partialStrengthen? strengthening.back.lift)
                        RawTerm.app =
                          some
                            (RawTerm.app targetForwardRaw.weaken
                              (RawTerm.app targetBackwardRaw.weaken
                                (RawTerm.var
                                  ⟨0, Nat.zero_lt_succ targetScope⟩)))
                    rw [forwardWeakenStrengthens, backwardVarAppStrengthens]
                    rfl
                  have leftInverseTypeStrengthens :
                      (equivIntroHetLeftInverseType carrierA forwardRaw
                          backwardRaw).partialStrengthen?
                          strengthening.back =
                        some (equivIntroHetLeftInverseType targetCarrierA
                          targetForwardRaw targetBackwardRaw) := by
                    have leftCodomainStrengthens :
                        (equivIntroHetLeftInverseCodomain carrierA
                            forwardRaw backwardRaw).partialStrengthen?
                            strengthening.back.lift =
                          some
                            (equivIntroHetLeftInverseCodomain targetCarrierA
                              targetForwardRaw targetBackwardRaw) := by
                      change
                        Option.mapThree
                          (carrierA.weaken.partialStrengthen?
                            strengthening.back.lift)
                          ((RawTerm.app backwardRaw.weaken
                            (RawTerm.app forwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ sourceScope⟩))
                            ).partialStrengthen? strengthening.back.lift)
                          (some (RawTerm.var
                            ⟨0, Nat.zero_lt_succ targetScope⟩))
                          Ty.id =
                            some
                              (equivIntroHetLeftInverseCodomain
                                targetCarrierA targetForwardRaw
                                targetBackwardRaw)
                      rw [carrierAWeakenStrengthens,
                        leftNestedAppStrengthens]
                      rfl
                    change
                      Option.mapTwo
                        (carrierA.partialStrengthen? strengthening.back)
                        ((equivIntroHetLeftInverseCodomain carrierA
                          forwardRaw backwardRaw).partialStrengthen?
                          strengthening.back.lift)
                        Ty.piTy =
                          some (equivIntroHetLeftInverseType targetCarrierA
                            targetForwardRaw targetBackwardRaw)
                    rw [carrierASuccess, leftCodomainStrengthens]
                    rfl
                  have rightInverseTypeStrengthens :
                      (equivIntroHetRightInverseType carrierB forwardRaw
                          backwardRaw).partialStrengthen?
                          strengthening.back =
                        some (equivIntroHetRightInverseType targetCarrierB
                          targetForwardRaw targetBackwardRaw) := by
                    have rightCodomainStrengthens :
                        (equivIntroHetRightInverseCodomain carrierB
                            forwardRaw backwardRaw).partialStrengthen?
                            strengthening.back.lift =
                          some
                            (equivIntroHetRightInverseCodomain targetCarrierB
                              targetForwardRaw targetBackwardRaw) := by
                      change
                        Option.mapThree
                          (carrierB.weaken.partialStrengthen?
                            strengthening.back.lift)
                          ((RawTerm.app forwardRaw.weaken
                            (RawTerm.app backwardRaw.weaken
                              (RawTerm.var
                                ⟨0, Nat.zero_lt_succ sourceScope⟩))
                            ).partialStrengthen? strengthening.back.lift)
                          (some (RawTerm.var
                            ⟨0, Nat.zero_lt_succ targetScope⟩))
                          Ty.id =
                            some
                              (equivIntroHetRightInverseCodomain
                                targetCarrierB targetForwardRaw
                                targetBackwardRaw)
                      rw [carrierBWeakenStrengthens,
                        rightNestedAppStrengthens]
                      rfl
                    change
                      Option.mapTwo
                        (carrierB.partialStrengthen? strengthening.back)
                        ((equivIntroHetRightInverseCodomain carrierB
                          forwardRaw backwardRaw).partialStrengthen?
                          strengthening.back.lift)
                        Ty.piTy =
                          some (equivIntroHetRightInverseType targetCarrierB
                            targetForwardRaw targetBackwardRaw)
                    rw [carrierBSuccess, rightCodomainStrengthens]
                    rfl
                  cases leftInvResult with
                  | mk targetLeftInvType targetLeftInvRaw targetLeftInv
                      leftInvTypeStrengthens leftInvRawStrengthens
                      leftInvTypeRenames leftInvRawRenames =>
                      rw [leftInverseTypeStrengthens] at leftInvTypeStrengthens
                      cases leftInvTypeStrengthens
                      cases rightInvResult with
                      | mk targetRightInvType targetRightInvRaw
                          targetRightInv rightInvTypeStrengthens
                          rightInvRawStrengthens rightInvTypeRenames
                          rightInvRawRenames =>
                          rw [rightInverseTypeStrengthens] at rightInvTypeStrengthens
                          cases rightInvTypeStrengthens
                          exact {
                            targetType :=
                              Ty.equiv targetCarrierA targetCarrierB
                            targetRaw :=
                              RawTerm.equivIntro targetForwardRaw
                                targetBackwardRaw
                            targetTerm :=
                              Term.equivIntroHet targetForward targetBackward
                                targetLeftInv targetRightInv
                            typeStrengthens := by
                              change
                                Option.mapTwo
                                  (carrierA.partialStrengthen?
                                    strengthening.back)
                                  (carrierB.partialStrengthen?
                                    strengthening.back)
                                  Ty.equiv =
                                    some (Ty.equiv targetCarrierA
                                      targetCarrierB)
                              rw [carrierASuccess, carrierBSuccess]
                              rfl
                            rawStrengthens := by
                              change
                                Option.mapTwo
                                  (forwardRaw.partialStrengthen?
                                    strengthening.back)
                                  (backwardRaw.partialStrengthen?
                                    strengthening.back)
                                  RawTerm.equivIntro =
                                    some (RawTerm.equivIntro
                                      targetForwardRaw targetBackwardRaw)
                              rw [forwardRawStrengthens,
                                backwardRawStrengthens]
                              rfl
                            typeRenames := by
                              exact
                                Ty.partialStrengthen?_imp_rename
                                  (Ty.equiv carrierA carrierB)
                                  strengthening.forward strengthening.back
                                  strengthening.injectsBack
                                  (Ty.equiv targetCarrierA targetCarrierB)
                                  (by
                                    change
                                      Option.mapTwo
                                        (carrierA.partialStrengthen?
                                          strengthening.back)
                                        (carrierB.partialStrengthen?
                                          strengthening.back)
                                        Ty.equiv =
                                          some (Ty.equiv targetCarrierA
                                            targetCarrierB)
                                    rw [carrierASuccess, carrierBSuccess]
                                    rfl)
                            rawRenames := by
                              cases forwardRawRenames
                              cases backwardRawRenames
                              rfl
                          }

/-- Universal typed partial strengthening dispatcher.

This is the public computational layer above the constructor-specific
certificates in this file.  It traverses a typed term once, recursively
strengthens the typed subterms, computes any schematic type/raw side
successes needed by value-shaped constructors, and delegates every
reconstruction step to the corresponding certificate.
-/
def partialStrengthenTyped? {mode : Mode} {level sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    {targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    Option (StrengtheningResult strengthening sourceTerm) :=
  match sourceTerm with
  | @Term.var _ _ _ _ position => by
      cases survives : strengthening.back position with
      | none => exact none
      | some targetPosition =>
          exact some
            (partialStrengthenTypedVarOfSurvives strengthening position
              targetPosition survives)
  | @Term.unit _ _ _ _ => by
      exact some (partialStrengthenTypedUnit strengthening)
  | @Term.lam _ _ _ _ domainType codomainType _ body => by
      cases domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCodomainType =>
              cases partialStrengthenTyped? body
                  (strengthening :=
                    strengthening.lift domainType targetDomainType
                      domainSuccess) with
              | none => exact none
              | some bodyResult =>
                  exact some
                    (partialStrengthenTypedLam domainSuccess
                      codomainSuccess bodyResult)
  | @Term.app _ _ _ _ domainType codomainType _ _ functionTerm
      argumentTerm => by
      cases domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCodomainType =>
              cases partialStrengthenTyped? functionTerm
                  (strengthening := strengthening) with
              | none => exact none
              | some functionResult =>
                  cases partialStrengthenTyped? argumentTerm
                      (strengthening := strengthening) with
                  | none => exact none
                  | some argumentResult =>
                      exact some
                        (partialStrengthenTypedApp domainSuccess
                          codomainSuccess functionResult argumentResult)
  | @Term.lamPi _ _ _ _ domainType _ _ body => by
      cases domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases partialStrengthenTyped? body
              (strengthening :=
                strengthening.lift domainType targetDomainType
                  domainSuccess) with
          | none => exact none
          | some bodyResult =>
              exact some
                (partialStrengthenTypedLamPi domainSuccess bodyResult)
  | @Term.appPi _ _ _ _ domainType codomainType _ _ functionTerm
      argumentTerm => by
      cases domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases codomainSuccess :
              codomainType.partialStrengthen? strengthening.back.lift with
          | none => exact none
          | some targetCodomainType =>
              cases partialStrengthenTyped? functionTerm
                  (strengthening := strengthening) with
              | none => exact none
              | some functionResult =>
                  cases partialStrengthenTyped? argumentTerm
                      (strengthening := strengthening) with
                  | none => exact none
                  | some argumentResult =>
                      exact some
                        (partialStrengthenTypedAppPi domainSuccess
                          codomainSuccess functionResult argumentResult)
  | @Term.pair _ _ _ _ _ secondType _ _ firstValue secondValue => by
      cases secondTypeSuccess :
          secondType.partialStrengthen? strengthening.back.lift with
      | none => exact none
      | some targetSecondType =>
          cases partialStrengthenTyped? firstValue
              (strengthening := strengthening) with
          | none => exact none
          | some firstResult =>
              cases partialStrengthenTyped? secondValue
                  (strengthening := strengthening) with
              | none => exact none
              | some secondResult =>
                  exact some
                    (partialStrengthenTypedPair secondTypeSuccess
                      firstResult secondResult)
  | @Term.fst _ _ _ _ firstType secondType _ pairTerm => by
      cases firstSuccess :
          firstType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetFirstType =>
          cases secondSuccess :
              secondType.partialStrengthen? strengthening.back.lift with
          | none => exact none
          | some targetSecondType =>
              cases partialStrengthenTyped? pairTerm
                  (strengthening := strengthening) with
              | none => exact none
              | some pairResult =>
                  exact some
                    (partialStrengthenTypedFst firstSuccess secondSuccess
                      pairResult)
  | @Term.snd _ _ _ _ firstType secondType _ pairTerm => by
      cases firstSuccess :
          firstType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetFirstType =>
          cases secondSuccess :
              secondType.partialStrengthen? strengthening.back.lift with
          | none => exact none
          | some targetSecondType =>
              cases partialStrengthenTyped? pairTerm
                  (strengthening := strengthening) with
              | none => exact none
              | some pairResult =>
                  exact some
                    (partialStrengthenTypedSnd firstSuccess secondSuccess
                      pairResult)
  | @Term.boolTrue _ _ _ _ => by
      exact some (partialStrengthenTypedBoolTrue strengthening)
  | @Term.boolFalse _ _ _ _ => by
      exact some (partialStrengthenTypedBoolFalse strengthening)
  | @Term.boolElim _ _ _ _ motiveType _ _ _ scrutinee thenBranch
      elseBranch => by
      cases motiveSuccess :
          motiveType.partialStrengthen? strengthening.back.lift with
      | none => exact none
      | some targetMotiveType =>
          cases partialStrengthenTyped? scrutinee
              (strengthening := strengthening) with
          | none => exact none
          | some scrutineeResult =>
              cases partialStrengthenTyped? thenBranch
                  (strengthening := strengthening) with
              | none => exact none
              | some thenResult =>
                  cases partialStrengthenTyped? elseBranch
                      (strengthening := strengthening) with
                  | none => exact none
                  | some elseResult =>
                      exact some
                        (partialStrengthenTypedBoolElim motiveSuccess
                          scrutineeResult thenResult elseResult)
  | @Term.natZero _ _ _ _ => by
      exact some (partialStrengthenTypedNatZero strengthening)
  | @Term.natSucc _ _ _ _ _ predecessor => by
      cases partialStrengthenTyped? predecessor
          (strengthening := strengthening) with
      | none => exact none
      | some predecessorResult =>
          exact some
            (partialStrengthenTypedNatSucc predecessorResult)
  | @Term.natElim _ _ _ _ _ _ _ _ scrutinee zeroBranch succBranch => by
      cases partialStrengthenTyped? scrutinee
          (strengthening := strengthening) with
      | none => exact none
      | some scrutineeResult =>
          cases partialStrengthenTyped? zeroBranch
              (strengthening := strengthening) with
          | none => exact none
          | some zeroResult =>
              cases partialStrengthenTyped? succBranch
                  (strengthening := strengthening) with
              | none => exact none
              | some succResult =>
                  exact some
                    (partialStrengthenTypedNatElim scrutineeResult
                      zeroResult succResult)
  | @Term.natRec _ _ _ _ _ _ _ _ scrutinee zeroBranch succBranch => by
      cases partialStrengthenTyped? scrutinee
          (strengthening := strengthening) with
      | none => exact none
      | some scrutineeResult =>
          cases partialStrengthenTyped? zeroBranch
              (strengthening := strengthening) with
          | none => exact none
          | some zeroResult =>
              cases partialStrengthenTyped? succBranch
                  (strengthening := strengthening) with
              | none => exact none
              | some succResult =>
                  exact some
                    (partialStrengthenTypedNatRec scrutineeResult
                      zeroResult succResult)
  | @Term.listNil _ _ _ _ elementType => by
      cases elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetElementType =>
          exact some
            (partialStrengthenTypedListNilOfType strengthening
              elementType targetElementType elementSuccess)
  | @Term.listCons _ _ _ _ _ _ _ headTerm tailTerm => by
      cases partialStrengthenTyped? headTerm
          (strengthening := strengthening) with
      | none => exact none
      | some headResult =>
          cases partialStrengthenTyped? tailTerm
              (strengthening := strengthening) with
          | none => exact none
          | some tailResult =>
              exact some
                (partialStrengthenTypedListCons headResult tailResult)
  | @Term.listElim _ _ _ _ _ _ _ _ _ scrutinee nilBranch consBranch => by
      cases partialStrengthenTyped? scrutinee
          (strengthening := strengthening) with
      | none => exact none
      | some scrutineeResult =>
          cases partialStrengthenTyped? nilBranch
              (strengthening := strengthening) with
          | none => exact none
          | some nilResult =>
              cases partialStrengthenTyped? consBranch
                  (strengthening := strengthening) with
              | none => exact none
              | some consResult =>
                  exact some
                    (partialStrengthenTypedListElim scrutineeResult
                      nilResult consResult)
  | @Term.optionNone _ _ _ _ elementType => by
      cases elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetElementType =>
          exact some
            (partialStrengthenTypedOptionNoneOfType strengthening
              elementType targetElementType elementSuccess)
  | @Term.optionSome _ _ _ _ _ _ valueTerm => by
      cases partialStrengthenTyped? valueTerm
          (strengthening := strengthening) with
      | none => exact none
      | some valueResult =>
          exact some (partialStrengthenTypedOptionSome valueResult)
  | @Term.optionMatch _ _ _ _ _ _ _ _ _ scrutinee noneBranch someBranch => by
      cases partialStrengthenTyped? scrutinee
          (strengthening := strengthening) with
      | none => exact none
      | some scrutineeResult =>
          cases partialStrengthenTyped? noneBranch
              (strengthening := strengthening) with
          | none => exact none
          | some noneResult =>
              cases partialStrengthenTyped? someBranch
                  (strengthening := strengthening) with
              | none => exact none
              | some someResult =>
                  exact some
                    (partialStrengthenTypedOptionMatch scrutineeResult
                      noneResult someResult)
  | @Term.eitherInl _ _ _ _ _ rightType _ valueTerm => by
      cases rightSuccess :
          rightType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetRightType =>
          cases partialStrengthenTyped? valueTerm
              (strengthening := strengthening) with
          | none => exact none
          | some valueResult =>
              exact some
                (partialStrengthenTypedEitherInlOfRightType
                  rightSuccess valueResult)
  | @Term.eitherInr _ _ _ _ leftType _ _ valueTerm => by
      cases leftSuccess :
          leftType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetLeftType =>
          cases partialStrengthenTyped? valueTerm
              (strengthening := strengthening) with
          | none => exact none
          | some valueResult =>
              exact some
                (partialStrengthenTypedEitherInrOfLeftType
                  leftSuccess valueResult)
  | @Term.eitherMatch _ _ _ _ _ _ _ _ _ _ scrutinee leftBranch rightBranch => by
      cases partialStrengthenTyped? scrutinee
          (strengthening := strengthening) with
      | none => exact none
      | some scrutineeResult =>
          cases partialStrengthenTyped? leftBranch
              (strengthening := strengthening) with
          | none => exact none
          | some leftResult =>
              cases partialStrengthenTyped? rightBranch
                  (strengthening := strengthening) with
              | none => exact none
              | some rightResult =>
                  exact some
                    (partialStrengthenTypedEitherMatch scrutineeResult
                      leftResult rightResult)
  | @Term.refl _ _ _ _ carrier rawWitness => by
      cases carrierSuccess : carrier.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetCarrier =>
          cases witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetWitness =>
              exact some
                (partialStrengthenTypedRefl carrierSuccess witnessSuccess)
  | @Term.idJ _ _ _ _ _ _ _ _ _ _ baseCase witness => by
      cases partialStrengthenTyped? baseCase
          (strengthening := strengthening) with
      | none => exact none
      | some baseResult =>
          cases partialStrengthenTyped? witness
              (strengthening := strengthening) with
          | none => exact none
          | some witnessResult =>
              exact some
                (partialStrengthenTypedIdJ baseResult witnessResult)
  | @Term.oeqRefl _ _ _ _ carrier rawWitness => by
      cases carrierSuccess : carrier.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetCarrier =>
          cases witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetWitness =>
              exact some
                (partialStrengthenTypedOeqRefl carrierSuccess witnessSuccess)
  | @Term.oeqJ _ _ _ _ _ _ _ _ _ _ baseCase witness => by
      cases partialStrengthenTyped? baseCase
          (strengthening := strengthening) with
      | none => exact none
      | some baseResult =>
          cases partialStrengthenTyped? witness
              (strengthening := strengthening) with
          | none => exact none
          | some witnessResult =>
              exact some
                (partialStrengthenTypedOeqJ baseResult witnessResult)
  | @Term.oeqFunext _ _ _ _ domainType codomainType leftFunctionRaw
      rightFunctionRaw _ pointwiseProof => by
      cases domainSuccess : domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCodomainType =>
              cases leftSuccess :
                  leftFunctionRaw.partialStrengthen? strengthening.back with
              | none => exact none
              | some targetLeftFunctionRaw =>
                  cases rightSuccess :
                      rightFunctionRaw.partialStrengthen? strengthening.back with
                  | none => exact none
                  | some targetRightFunctionRaw =>
                      cases partialStrengthenTyped? pointwiseProof
                          (strengthening := strengthening) with
                      | none => exact none
                      | some pointwiseResult =>
                          exact some
                            (partialStrengthenTypedOeqFunext domainType
                              codomainType targetDomainType
                              targetCodomainType leftFunctionRaw
                              rightFunctionRaw targetLeftFunctionRaw
                              targetRightFunctionRaw domainSuccess
                              codomainSuccess leftSuccess rightSuccess
                              pointwiseResult)
  | @Term.idStrictRefl _ _ _ _ modeIsStrict carrier rawWitness => by
      cases carrierSuccess : carrier.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetCarrier =>
          cases witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetWitness =>
              exact some
                (partialStrengthenTypedIdStrictRefl modeIsStrict
                  carrierSuccess witnessSuccess)
  | @Term.idStrictRec _ _ _ _ modeIsStrict _ _ _ _ _ _ baseCase witness => by
      cases partialStrengthenTyped? baseCase
          (strengthening := strengthening) with
      | none => exact none
      | some baseResult =>
          cases partialStrengthenTyped? witness
              (strengthening := strengthening) with
          | none => exact none
          | some witnessResult =>
              exact some
                (partialStrengthenTypedIdStrictRec modeIsStrict
                  baseResult witnessResult)
  | @Term.modIntro _ _ _ _ _ _ innerTerm => by
      cases partialStrengthenTyped? innerTerm
          (strengthening := strengthening) with
      | none => exact none
      | some innerResult =>
          exact some (partialStrengthenTypedModIntro innerResult)
  | @Term.modElim _ _ _ _ _ _ innerTerm => by
      cases partialStrengthenTyped? innerTerm
          (strengthening := strengthening) with
      | none => exact none
      | some innerResult =>
          exact some (partialStrengthenTypedModElim innerResult)
  | @Term.subsume _ _ _ _ _ _ innerTerm => by
      cases partialStrengthenTyped? innerTerm
          (strengthening := strengthening) with
      | none => exact none
      | some innerResult =>
          exact some (partialStrengthenTypedSubsume innerResult)
  | @Term.interval0 _ _ _ _ => by
      exact some (partialStrengthenTypedInterval0 strengthening)
  | @Term.interval1 _ _ _ _ => by
      exact some (partialStrengthenTypedInterval1 strengthening)
  | @Term.intervalOpp _ _ _ _ _ innerValue => by
      cases partialStrengthenTyped? innerValue
          (strengthening := strengthening) with
      | none => exact none
      | some innerResult =>
          exact some (partialStrengthenTypedIntervalOpp innerResult)
  | @Term.intervalMeet _ _ _ _ _ _ leftValue rightValue => by
      cases partialStrengthenTyped? leftValue
          (strengthening := strengthening) with
      | none => exact none
      | some leftResult =>
          cases partialStrengthenTyped? rightValue
              (strengthening := strengthening) with
          | none => exact none
          | some rightResult =>
              exact some
                (partialStrengthenTypedIntervalMeet leftResult rightResult)
  | @Term.intervalJoin _ _ _ _ _ _ leftValue rightValue => by
      cases partialStrengthenTyped? leftValue
          (strengthening := strengthening) with
      | none => exact none
      | some leftResult =>
          cases partialStrengthenTyped? rightValue
              (strengthening := strengthening) with
          | none => exact none
          | some rightResult =>
              exact some
                (partialStrengthenTypedIntervalJoin leftResult rightResult)
  | @Term.pathLam _ _ _ _ modeIsUnivalent carrierType leftEndpoint
      rightEndpoint _ body => by
      cases carrierSuccess :
          carrierType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetCarrierType =>
          cases leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetLeftEndpoint =>
              cases rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => exact none
              | some targetRightEndpoint =>
                  cases partialStrengthenTyped? body
                      (strengthening :=
                        strengthening.lift Ty.interval Ty.interval rfl) with
                  | none => exact none
                  | some bodyResult =>
                      exact some
                        (partialStrengthenTypedPathLam modeIsUnivalent
                          carrierSuccess leftSuccess rightSuccess bodyResult)
  | @Term.pathApp _ _ _ _ modeIsUnivalent _ _ _ _ _ pathTerm intervalTerm => by
      cases partialStrengthenTyped? pathTerm
          (strengthening := strengthening) with
      | none => exact none
      | some pathResult =>
          cases partialStrengthenTyped? intervalTerm
              (strengthening := strengthening) with
          | none => exact none
          | some intervalResult =>
              exact some
                (partialStrengthenTypedPathApp modeIsUnivalent
                  pathResult intervalResult)
  | @Term.glueIntro _ _ _ _ modeIsUnivalent baseType boundaryWitness _ _
      baseValue partialValue => by
      cases baseTypeSuccess : baseType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetBaseType =>
          cases boundarySuccess :
              boundaryWitness.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetBoundaryWitness =>
              cases partialStrengthenTyped? baseValue
                  (strengthening := strengthening) with
              | none => exact none
              | some baseResult =>
                  cases partialStrengthenTyped? partialValue
                      (strengthening := strengthening) with
                  | none => exact none
                  | some partialResult =>
                      exact some
                        (partialStrengthenTypedGlueIntro modeIsUnivalent
                          baseType targetBaseType boundaryWitness
                          targetBoundaryWitness baseTypeSuccess
                          boundarySuccess baseResult partialResult)
  | @Term.glueElim _ _ _ _ modeIsUnivalent baseType boundaryWitness _
      gluedValue => by
      cases baseSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => exact none
      | some _ =>
          cases boundarySuccess :
              boundaryWitness.partialStrengthen? strengthening.back with
          | none => exact none
          | some _ =>
              cases partialStrengthenTyped? gluedValue
                  (strengthening := strengthening) with
              | none => exact none
              | some gluedResult =>
                  exact some
                    (partialStrengthenTypedGlueElim modeIsUnivalent
                      baseSuccess boundarySuccess gluedResult)
  | @Term.transp _ _ _ _ modeIsUnivalent universeLevel universeLevelLt
      sourceType targetType sourceTypeRaw targetTypeRaw _ _ typePath
      sourceValue => by
      cases sourceTypeSuccess :
          sourceType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetSourceType =>
          cases targetTypeSuccess :
              targetType.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetTargetType =>
              cases sourceTypeRawSuccess :
                  sourceTypeRaw.partialStrengthen? strengthening.back with
              | none => exact none
              | some targetSourceTypeRaw =>
                  cases targetTypeRawSuccess :
                      targetTypeRaw.partialStrengthen? strengthening.back with
                  | none => exact none
                  | some targetTargetTypeRaw =>
                      cases partialStrengthenTyped? typePath
                          (strengthening := strengthening) with
                      | none => exact none
                      | some pathResult =>
                          cases partialStrengthenTyped? sourceValue
                              (strengthening := strengthening) with
                          | none => exact none
                          | some sourceResult =>
                              exact some
                                (partialStrengthenTypedTransp
                                  modeIsUnivalent universeLevel
                                  universeLevelLt sourceType targetType
                                  targetSourceType targetTargetType
                                  sourceTypeRaw targetTypeRaw
                                  targetSourceTypeRaw targetTargetTypeRaw
                                  sourceTypeSuccess targetTypeSuccess
                                  sourceTypeRawSuccess targetTypeRawSuccess
                                  pathResult sourceResult)
  | @Term.hcomp _ _ _ _ modeIsUnivalent _ _ _ sidesValue capValue => by
      cases partialStrengthenTyped? sidesValue
          (strengthening := strengthening) with
      | none => exact none
      | some sidesResult =>
          cases partialStrengthenTyped? capValue
              (strengthening := strengthening) with
          | none => exact none
          | some capResult =>
              exact some
                (partialStrengthenTypedHcomp modeIsUnivalent sidesResult
                  capResult)
  | @Term.hcompPath _ _ _ _ modeIsUnivalent _ leftEndpoint rightEndpoint
      _ _ sidesPath capValue => by
      cases partialStrengthenTyped? sidesPath
          (strengthening := strengthening) with
      | none => exact none
      | some sidesResult =>
          cases partialStrengthenTyped? capValue
              (strengthening := strengthening) with
          | none => exact none
          | some capResult =>
              exact some
                (partialStrengthenTypedHcompPath modeIsUnivalent
                  leftEndpoint rightEndpoint sidesResult capResult)
  | @Term.recordIntro _ _ _ _ _ _ firstField => by
      cases partialStrengthenTyped? firstField
          (strengthening := strengthening) with
      | none => exact none
      | some fieldResult =>
          exact some (partialStrengthenTypedRecordIntro fieldResult)
  | @Term.recordProj _ _ _ _ singleFieldType _ recordValue => by
      cases fieldSuccess :
          singleFieldType.partialStrengthen? strengthening.back with
      | none => exact none
      | some _ =>
          cases partialStrengthenTyped? recordValue
              (strengthening := strengthening) with
          | none => exact none
          | some recordResult =>
              exact some
                (partialStrengthenTypedRecordProj fieldSuccess recordResult)
  | @Term.refineIntro _ _ _ _ _ predicate _ _ baseValue predicateProof => by
      cases predicateSuccess :
          predicate.partialStrengthen? strengthening.back.lift with
      | none => exact none
      | some targetPredicate =>
          cases partialStrengthenTyped? baseValue
              (strengthening := strengthening) with
          | none => exact none
          | some baseResult =>
              cases partialStrengthenTyped? predicateProof
                  (strengthening := strengthening) with
              | none => exact none
              | some proofResult =>
                  exact some
                    (partialStrengthenTypedRefineIntro predicateSuccess
                      baseResult proofResult)
  | @Term.refineElim _ _ _ _ baseType predicate _ refinedValue => by
      cases baseSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => exact none
      | some _ =>
          cases predicateSuccess :
              predicate.partialStrengthen? strengthening.back.lift with
          | none => exact none
          | some _ =>
              cases partialStrengthenTyped? refinedValue
                  (strengthening := strengthening) with
              | none => exact none
              | some refinedResult =>
                  exact some
                    (partialStrengthenTypedRefineElim baseSuccess
                      predicateSuccess refinedResult)
  | @Term.codataUnfold _ _ _ _ _ outputType _ _ initialState transition => by
      cases outputSuccess :
          outputType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetOutputType =>
          cases partialStrengthenTyped? initialState
              (strengthening := strengthening) with
          | none => exact none
          | some stateResult =>
              cases partialStrengthenTyped? transition
                  (strengthening := strengthening) with
              | none => exact none
              | some transitionResult =>
                  exact some
                    (partialStrengthenTypedCodataUnfold outputSuccess
                      stateResult transitionResult)
  | @Term.codataDest _ _ _ _ stateType outputType _ codataValue => by
      cases stateSuccess :
          stateType.partialStrengthen? strengthening.back with
      | none => exact none
      | some _ =>
          cases outputSuccess :
              outputType.partialStrengthen? strengthening.back with
          | none => exact none
          | some _ =>
              cases partialStrengthenTyped? codataValue
                  (strengthening := strengthening) with
              | none => exact none
              | some codataResult =>
                  exact some
                    (partialStrengthenTypedCodataDest stateSuccess
                      outputSuccess codataResult)
  | @Term.sessionSend _ _ _ _ protocolStep _ _ _ channel payload => by
      cases protocolSuccess :
          protocolStep.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetProtocolStep =>
          cases partialStrengthenTyped? channel
              (strengthening := strengthening) with
          | none => exact none
          | some channelResult =>
              cases partialStrengthenTyped? payload
                  (strengthening := strengthening) with
              | none => exact none
              | some payloadResult =>
                  exact some
                    (partialStrengthenTypedSessionSend protocolSuccess
                      channelResult payloadResult)
  | @Term.sessionRecv _ _ _ _ protocolStep _ channel => by
      cases protocolSuccess :
          protocolStep.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetProtocolStep =>
          cases partialStrengthenTyped? channel
              (strengthening := strengthening) with
          | none => exact none
          | some channelResult =>
              exact some
                (partialStrengthenTypedSessionRecv protocolSuccess
                  channelResult)
  | @Term.effectPerform _ _ _ _ effectTag effectRow operationSignature
      canPerformOperation _ _ operationTag arguments => by
      cases effectTagSuccess :
          effectTag.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetEffectTag =>
          cases argumentCarrierSuccess :
              operationSignature.argumentCarrier.partialStrengthen?
                strengthening.back with
          | none => exact none
          | some targetArgumentCarrier =>
              cases resultCarrierSuccess :
                  operationSignature.resultCarrier.partialStrengthen?
                    strengthening.back with
              | none => exact none
              | some targetResultCarrier =>
                  cases partialStrengthenTyped? operationTag
                      (strengthening := strengthening) with
                  | none => exact none
                  | some operationResult =>
                      cases partialStrengthenTyped? arguments
                          (strengthening := strengthening) with
                      | none => exact none
                      | some argumentsResult =>
                          exact some
                            (partialStrengthenTypedEffectPerform effectTag
                              targetEffectTag effectRow operationSignature
                              targetArgumentCarrier targetResultCarrier
                              canPerformOperation effectTagSuccess
                              argumentCarrierSuccess resultCarrierSuccess
                              operationResult argumentsResult)
  | @Term.universeCode _ _ _ _ innerLevel outerLevel cumulOk levelLe => by
      exact some
        (partialStrengthenTypedUniverseCode strengthening innerLevel
          outerLevel cumulOk levelLe)
  | @Term.cumulUp _ _ _ _ lowerLevel higherLevel cumulMonotone levelLeLow
      levelLeHigh _ typeCode => by
      cases partialStrengthenTyped? typeCode
          (strengthening := strengthening) with
      | none => exact none
      | some codeResult =>
          exact some
            (partialStrengthenTypedCumulUp lowerLevel higherLevel
              cumulMonotone levelLeLow levelLeHigh codeResult)
  | @Term.equivReflId _ _ _ _ carrier => by
      cases carrierSuccess : carrier.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetCarrier =>
          exact some
            (partialStrengthenTypedEquivReflId carrier targetCarrier
              carrierSuccess)
  | @Term.funextRefl _ _ _ _ domainType codomainType applyRaw => by
      cases domainSuccess : domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCodomainType =>
              cases applySuccess :
                  applyRaw.partialStrengthen? strengthening.back.lift with
              | none => exact none
              | some targetApplyRaw =>
                  exact some
                    (partialStrengthenTypedFunextRefl domainType
                      codomainType targetDomainType targetCodomainType
                      applyRaw targetApplyRaw domainSuccess
                      codomainSuccess applySuccess)
  | @Term.equivReflIdAtId _ _ _ _ innerLevel innerLevelLt carrier
      carrierRaw => by
      cases carrierSuccess : carrier.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetCarrier =>
          cases carrierRawSuccess :
              carrierRaw.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCarrierRaw =>
              exact some
                (partialStrengthenTypedEquivReflIdAtId innerLevel
                  innerLevelLt carrier targetCarrier carrierRaw
                  targetCarrierRaw carrierSuccess carrierRawSuccess)
  | @Term.funextReflAtId _ _ _ _ domainType codomainType applyRaw => by
      cases domainSuccess : domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCodomainType =>
              cases applySuccess :
                  applyRaw.partialStrengthen? strengthening.back.lift with
              | none => exact none
              | some targetApplyRaw =>
                  exact some
                    (partialStrengthenTypedFunextReflAtId domainType
                      codomainType targetDomainType targetCodomainType
                      applyRaw targetApplyRaw domainSuccess
                      codomainSuccess applySuccess)
  | @Term.equivIntroHet _ _ _ _ _ _ _ _ _ _ forward backward leftInv
      rightInv => by
      cases partialStrengthenTyped? forward
          (strengthening := strengthening) with
      | none => exact none
      | some forwardResult =>
          cases partialStrengthenTyped? backward
              (strengthening := strengthening) with
          | none => exact none
          | some backwardResult =>
              cases partialStrengthenTyped? leftInv
                  (strengthening := strengthening) with
              | none => exact none
              | some leftInvResult =>
                  cases partialStrengthenTyped? rightInv
                      (strengthening := strengthening) with
                  | none => exact none
                  | some rightInvResult =>
                      exact some
                        (partialStrengthenTypedEquivIntroHet forwardResult
                          backwardResult leftInvResult rightInvResult)
  | @Term.equivApp _ _ _ _ _ _ _ _ equivTerm argumentTerm => by
      cases partialStrengthenTyped? equivTerm
          (strengthening := strengthening) with
      | none => exact none
      | some equivResult =>
          cases partialStrengthenTyped? argumentTerm
              (strengthening := strengthening) with
          | none => exact none
          | some argumentResult =>
              exact some
                (partialStrengthenTypedEquivApp equivResult argumentResult)
  | @Term.uaIntroHet _ _ _ _ innerLevel innerLevelLt carrierA carrierB
      carrierARaw carrierBRaw forwardRaw backwardRaw equivWitness => by
      cases carrierASuccess : carrierA.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetCarrierA =>
          cases carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCarrierB =>
              cases carrierARawSuccess :
                  carrierARaw.partialStrengthen? strengthening.back with
              | none => exact none
              | some targetCarrierARaw =>
                  cases carrierBRawSuccess :
                      carrierBRaw.partialStrengthen? strengthening.back with
                  | none => exact none
                  | some targetCarrierBRaw =>
                      cases forwardRawSuccess :
                          forwardRaw.partialStrengthen?
                            strengthening.back with
                      | none => exact none
                      | some targetForwardRaw =>
                          cases backwardRawSuccess :
                              backwardRaw.partialStrengthen?
                                strengthening.back with
                          | none => exact none
                          | some targetBackwardRaw =>
                              cases partialStrengthenTyped? equivWitness
                                  (strengthening := strengthening) with
                              | none => exact none
                              | some equivResult =>
                                  exact some
                                    (partialStrengthenTypedUaIntroHet
                                      innerLevel innerLevelLt targetCarrierA
                                      targetCarrierB carrierARaw carrierBRaw
                                      targetCarrierARaw targetCarrierBRaw
                                      targetForwardRaw targetBackwardRaw
                                      carrierASuccess carrierBSuccess
                                      carrierARawSuccess carrierBRawSuccess
                                      forwardRawSuccess backwardRawSuccess
                                      equivResult)
  | @Term.funextIntroHet _ _ _ _ domainType codomainType applyARaw
      applyBRaw => by
      cases domainSuccess : domainType.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainType =>
          cases codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCodomainType =>
              cases applyASuccess :
                  applyARaw.partialStrengthen? strengthening.back.lift with
              | none => exact none
              | some targetApplyARaw =>
                  cases applyBSuccess :
                      applyBRaw.partialStrengthen? strengthening.back.lift with
                  | none => exact none
                  | some targetApplyBRaw =>
                      exact some
                        (partialStrengthenTypedFunextIntroHet domainType
                          codomainType targetDomainType targetCodomainType
                          applyARaw applyBRaw targetApplyARaw
                          targetApplyBRaw domainSuccess codomainSuccess
                          applyASuccess applyBSuccess)
  | @Term.arrowCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw => by
      cases domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainCodeRaw =>
          cases codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetCodomainCodeRaw =>
              exact some
                (partialStrengthenTypedArrowCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.piTyCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw => by
      cases domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainCodeRaw =>
          cases codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back.lift with
          | none => exact none
          | some targetCodomainCodeRaw =>
              exact some
                (partialStrengthenTypedPiTyCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.sigmaTyCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw => by
      cases domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetDomainCodeRaw =>
          cases codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back.lift with
          | none => exact none
          | some targetCodomainCodeRaw =>
              exact some
                (partialStrengthenTypedSigmaTyCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.productCode _ _ _ _ outerLevel levelLe firstCodeRaw
      secondCodeRaw => by
      cases firstSuccess :
          firstCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetFirstCodeRaw =>
          cases secondSuccess :
              secondCodeRaw.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetSecondCodeRaw =>
              exact some
                (partialStrengthenTypedProductCode outerLevel levelLe
                  firstCodeRaw secondCodeRaw targetFirstCodeRaw
                  targetSecondCodeRaw firstSuccess secondSuccess)
  | @Term.sumCode _ _ _ _ outerLevel levelLe leftCodeRaw rightCodeRaw => by
      cases leftSuccess :
          leftCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetLeftCodeRaw =>
          cases rightSuccess :
              rightCodeRaw.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetRightCodeRaw =>
              exact some
                (partialStrengthenTypedSumCode outerLevel levelLe
                  leftCodeRaw rightCodeRaw targetLeftCodeRaw
                  targetRightCodeRaw leftSuccess rightSuccess)
  | @Term.listCode _ _ _ _ outerLevel levelLe elementCodeRaw => by
      cases elementSuccess :
          elementCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetElementCodeRaw =>
          exact some
            (partialStrengthenTypedListCode outerLevel levelLe
              elementCodeRaw targetElementCodeRaw elementSuccess)
  | @Term.optionCode _ _ _ _ outerLevel levelLe elementCodeRaw => by
      cases elementSuccess :
          elementCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetElementCodeRaw =>
          exact some
            (partialStrengthenTypedOptionCode outerLevel levelLe
              elementCodeRaw targetElementCodeRaw elementSuccess)
  | @Term.eitherCode _ _ _ _ outerLevel levelLe leftCodeRaw rightCodeRaw => by
      cases leftSuccess :
          leftCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetLeftCodeRaw =>
          cases rightSuccess :
              rightCodeRaw.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetRightCodeRaw =>
              exact some
                (partialStrengthenTypedEitherCode outerLevel levelLe
                  leftCodeRaw rightCodeRaw targetLeftCodeRaw
                  targetRightCodeRaw leftSuccess rightSuccess)
  | @Term.idCode _ _ _ _ outerLevel levelLe typeCodeRaw leftRaw rightRaw => by
      cases typeSuccess :
          typeCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetTypeCodeRaw =>
          cases leftSuccess : leftRaw.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetLeftRaw =>
              cases rightSuccess :
                  rightRaw.partialStrengthen? strengthening.back with
              | none => exact none
              | some targetRightRaw =>
                  exact some
                    (partialStrengthenTypedIdCode outerLevel levelLe
                      typeCodeRaw leftRaw rightRaw targetTypeCodeRaw
                      targetLeftRaw targetRightRaw typeSuccess leftSuccess
                      rightSuccess)
  | @Term.equivCode _ _ _ _ outerLevel levelLe leftTypeCodeRaw
      rightTypeCodeRaw => by
      cases leftSuccess :
          leftTypeCodeRaw.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetLeftTypeCodeRaw =>
          cases rightSuccess :
              rightTypeCodeRaw.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetRightTypeCodeRaw =>
              exact some
                (partialStrengthenTypedEquivCode outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw targetLeftTypeCodeRaw
                  targetRightTypeCodeRaw leftSuccess rightSuccess)
  | @Term.uaToEquiv _ _ _ _ innerLevel innerLevelLt leftTy rightTy
      leftTyRaw rightTyRaw _ proof => by
      cases leftTySuccess : leftTy.partialStrengthen? strengthening.back with
      | none => exact none
      | some targetLeftTy =>
          cases rightTySuccess :
              rightTy.partialStrengthen? strengthening.back with
          | none => exact none
          | some targetRightTy =>
              cases leftRawSuccess :
                  leftTyRaw.partialStrengthen? strengthening.back with
              | none => exact none
              | some targetLeftTyRaw =>
                  cases rightRawSuccess :
                      rightTyRaw.partialStrengthen? strengthening.back with
                  | none => exact none
                  | some targetRightTyRaw =>
                      cases partialStrengthenTyped? proof
                          (strengthening := strengthening) with
                      | none => exact none
                      | some proofResult =>
                          exact some
                            (partialStrengthenTypedUaToEquiv innerLevel
                              innerLevelLt leftTy rightTy targetLeftTy
                              targetRightTy leftTyRaw rightTyRaw
                              targetLeftTyRaw targetRightTyRaw
                              leftTySuccess rightTySuccess leftRawSuccess
                              rightRawSuccess proofResult)
  | @Term.equivApply _ _ _ _ _ _ _ _ equivTerm argumentTerm => by
      cases partialStrengthenTyped? equivTerm
          (strengthening := strengthening) with
      | none => exact none
      | some equivResult =>
          cases partialStrengthenTyped? argumentTerm
              (strengthening := strengthening) with
          | none => exact none
          | some argumentResult =>
              exact some
                (partialStrengthenTypedEquivApply equivResult argumentResult)

/-- Single-newest-slot typed strengthening.

This is the semantic strengthening variant for a term in
`context.cons newType`: it returns a fully typed predecessor exactly when
the type index, raw index, and every typed subterm survive
`PartialRawRenaming.dropNewest`.
-/
def strengthenTyped? {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw) :
    Option (StrengtheningResult
      (ContextStrengthening.dropNewest context newType) sourceTerm) :=
  partialStrengthenTyped? sourceTerm
    (ContextStrengthening.dropNewest context newType)

/-- Successful single-newest-slot typed strengthening gives the
canonical weakening equations for the source term's type and raw
indices.

This is the typed counterpart of
`Term.strengthen?_imp_indices_weaken`; it exposes the equations carried
by `StrengtheningResult` without making consumers destruct the result
record by hand.
-/
theorem strengthenTyped?_imp_indices_weaken
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw)
    (result : StrengtheningResult
      (ContextStrengthening.dropNewest context newType) sourceTerm)
    (_success : strengthenTyped? sourceTerm = some result) :
    sourceType = result.targetType.weaken ∧
      sourceRaw = result.targetRaw.weaken := by
  exact ⟨result.typeRenames, result.rawRenames⟩

/-- Typed newest-slot use predicate.

The predicate is deliberately defined by the typed strengthening
dispatcher, not only by raw syntax: `false` means a typed predecessor was
actually reconstructed through the context morphism.
-/
def usesNewestSlotTyped? {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw) :
    Bool :=
  (strengthenTyped? sourceTerm).isNone

/-- Structural typed unweakening.

When both indices are syntactically known weakenings, typed
strengthening reconstructs an exact predecessor at the original type and
raw indices.  The casts are justified by the existing all-constructors
type/raw facts `Ty.strengthen?_weaken` and `RawTerm.strengthen?_weaken`.
-/
def unweaken? {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) sourceType.weaken sourceRaw.weaken) :
    Option (Term context sourceType sourceRaw) :=
  match strengthenTyped? weakenedTerm with
  | none => none
  | some result =>
      match result with
      | StrengtheningResult.mk targetType targetRaw targetTerm
          typeStrengthens rawStrengthens _ _ =>
          have targetTypeEq : targetType = sourceType := by
            change sourceType.weaken.strengthen? = some targetType at typeStrengthens
            rw [Ty.strengthen?_weaken sourceType] at typeStrengthens
            cases typeStrengthens
            rfl
          have targetRawEq : targetRaw = sourceRaw := by
            change sourceRaw.weaken.strengthen? = some targetRaw at rawStrengthens
            rw [RawTerm.strengthen?_weaken sourceRaw] at rawStrengthens
            cases rawStrengthens
            rfl
          by
            cases targetTypeEq
            cases targetRawEq
            exact some targetTerm

/-- Semantic typed strengthening witness from the boolean predicate.

This is the typed counterpart of `not_usesNewestSlot?_imp_indices_weaken`:
the witness is a full `StrengtheningResult`, not just strengthened
indices.
-/
theorem not_usesNewestSlotTyped?_imp_strengthenTyped?_some
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceType : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceType sourceRaw)
    (slotIsUnused : usesNewestSlotTyped? sourceTerm = false) :
    ∃ result : StrengtheningResult
        (ContextStrengthening.dropNewest context newType) sourceTerm,
      strengthenTyped? sourceTerm = some result := by
  unfold usesNewestSlotTyped? at slotIsUnused
  cases success : strengthenTyped? sourceTerm with
  | none =>
      rw [success] at slotIsUnused
      cases slotIsUnused
  | some result =>
      exact ⟨result, rfl⟩

end Term

end LeanFX2
