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
interval argument.

App-pattern: takes `carrierSuccess`, `leftSuccess`, `rightSuccess` as
explicit parameters lifted from the dispatcher's three nested option-
splits on the path carrier type, left endpoint, and right endpoint
respectively.  Wrapper body destructures both `pathResult` and
`intervalResult`, aligns the `Ty.path` shape of the path's
`pathTypeStrengthens` via the standard `Option.mapThree` discharge
recipe, then delegates to `partialStrengthenTypedPathAppOfSuccess`.
Sister of `partialStrengthenTypedHcompPath` (Phase 42) — same
3-option-split shape applied to the second cubical path-elimination
producer. -/
def partialStrengthenTypedPathApp {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (pathResult : StrengtheningResult strengthening pathTerm)
    (intervalResult : StrengtheningResult strengthening intervalTerm) :
    StrengtheningResult strengthening
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPathTerm pathTypeStrengthens
      pathRawStrengthens pathTypeRenames pathRawRenames =>
      have expectedPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint
              rightEndpoint).partialStrengthen?
              strengthening.back =
            some (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint) := by
        change
          Option.mapThree
            (carrierType.partialStrengthen? strengthening.back)
            (leftEndpoint.partialStrengthen? strengthening.back)
            (rightEndpoint.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
        rw [carrierSuccess, leftSuccess, rightSuccess]
        rfl
      rw [expectedPathTypeStrengthens] at pathTypeStrengthens
      cases pathTypeStrengthens
      cases intervalResult with
      | mk targetIntervalType targetIntervalRaw targetIntervalTerm
          intervalTypeStrengthens intervalRawStrengthens
          intervalTypeRenames intervalRawRenames =>
          cases intervalTypeStrengthens
          exact partialStrengthenTypedPathAppOfSuccess
            modeIsUnivalent targetPathTerm targetIntervalTerm
            carrierSuccess leftSuccess rightSuccess
            pathRawStrengthens intervalRawStrengthens
            pathRawRenames intervalRawRenames

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
    {targetElementType : Ty level targetScope}
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
    (elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType)
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (nilResult : StrengtheningResult strengthening nilBranch)
    (consResult : StrengtheningResult strengthening consBranch) :
    StrengtheningResult strengthening
      (Term.listElim scrutinee nilBranch consBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      have expectedScrutineeTypeStrengthens :
          (Ty.listType elementType).partialStrengthen?
              strengthening.back =
            some (Ty.listType targetElementType) := by
        change
          (match elementType.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (Ty.listType strengthenedElement)
          | none => none) = some (Ty.listType targetElementType)
        rw [elementSuccess]
      rw [expectedScrutineeTypeStrengthens] at scrutineeTypeStrengthens
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
    {targetElementType : Ty level targetScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType)
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (noneResult : StrengtheningResult strengthening noneBranch)
    (someResult : StrengtheningResult strengthening someBranch) :
    StrengtheningResult strengthening
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      have expectedScrutineeTypeStrengthens :
          (Ty.optionType elementType).partialStrengthen?
              strengthening.back =
            some (Ty.optionType targetElementType) := by
        change
          (match elementType.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (Ty.optionType strengthenedElement)
          | none => none) = some (Ty.optionType targetElementType)
        rw [elementSuccess]
      rw [expectedScrutineeTypeStrengthens] at scrutineeTypeStrengthens
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
    {targetLeftType targetRightType targetMotiveType : Ty level targetScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (leftSuccess :
      leftType.partialStrengthen? strengthening.back = some targetLeftType)
    (rightSuccess :
      rightType.partialStrengthen? strengthening.back = some targetRightType)
    (motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (scrutineeResult : StrengtheningResult strengthening scrutinee)
    (leftResult : StrengtheningResult strengthening leftBranch)
    (rightResult : StrengtheningResult strengthening rightBranch) :
    StrengtheningResult strengthening
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      have expectedScrutineeTypeStrengthens :
          (Ty.eitherType leftType rightType).partialStrengthen?
              strengthening.back =
            some (Ty.eitherType targetLeftType targetRightType) := by
        change
          Option.mapTwo
            (leftType.partialStrengthen? strengthening.back)
            (rightType.partialStrengthen? strengthening.back)
            Ty.eitherType =
              some (Ty.eitherType targetLeftType targetRightType)
        rw [leftSuccess, rightSuccess]
        rfl
      rw [expectedScrutineeTypeStrengthens] at scrutineeTypeStrengthens
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
          rw [leftSuccess, motiveSuccess] at leftTypeStrengthens
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
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
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
          have expectedWitnessTypeStrengthens :
              (Ty.id carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.id targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.id =
                  some (Ty.id targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
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
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
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
          have expectedWitnessTypeStrengthens :
              (Ty.oeq carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.oeq targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.oeq =
                  some (Ty.oeq targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
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
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
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
          have expectedWitnessTypeStrengthens :
              (Ty.idStrict carrier leftEndpoint
                  rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.idStrict targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.idStrict =
                  some (Ty.idStrict targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
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
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivResult : StrengtheningResult strengthening equivTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.equivApp equivTerm argumentTerm) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
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
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
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
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivResult : StrengtheningResult strengthening equivTerm)
    (argumentResult : StrengtheningResult strengthening argumentTerm) :
    StrengtheningResult strengthening
      (Term.equivApply equivTerm argumentTerm) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
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
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
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
    (_sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (_sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (_targetTypeRawStrengthens :
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
strengthened path carrier for the sides and aligning the cap carrier.

App-pattern: takes `carrierSuccess`, `leftSuccess`, `rightSuccess` as
explicit parameters lifted from the dispatcher's three nested option-
splits on the path carrier type, left endpoint, and right endpoint
respectively.  The body destructures both `sidesPathResult` and
`capResult`, aligns the `Ty.path` shape of `sidesPathType` and the
`carrierType` of the cap, then delegates to
`partialStrengthenTypedHcompPathOfSuccess`.  Extends the recipe from
Phase 39/40/41 (2-option) to 3-option wrappers — the App-pattern
remains uniform: every option-split lifts to a wrapper parameter, the
leaf consumes all witnesses, and soundness mirrors the case cascade. -/
def partialStrengthenTypedHcompPath {mode : Mode} {level : Nat}
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
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (sidesPathResult : StrengtheningResult strengthening sidesPath)
    (capResult : StrengtheningResult strengthening capValue) :
    StrengtheningResult strengthening
      (Term.hcompPath (context := sourceCtx) modeIsUnivalent
        leftEndpoint rightEndpoint sidesPath capValue) := by
  cases sidesPathResult with
  | mk targetSidesPathType targetSidesPathRaw targetSidesPath
      sidesPathTypeStrengthens sidesPathRawStrengthens
      sidesPathTypeRenames sidesPathRawRenames =>
      have expectedSidesPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint rightEndpoint).partialStrengthen?
              strengthening.back =
            some (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint) := by
        change
          Option.mapThree
            (carrierType.partialStrengthen? strengthening.back)
            (leftEndpoint.partialStrengthen? strengthening.back)
            (rightEndpoint.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
        rw [carrierSuccess, leftSuccess, rightSuccess]
        rfl
      rw [expectedSidesPathTypeStrengthens] at sidesPathTypeStrengthens
      cases sidesPathTypeStrengthens
      cases capResult with
      | mk targetCapType targetCapRaw targetCapValue
          capTypeStrengthens capRawStrengthens capTypeRenames
          capRawRenames =>
          rw [carrierSuccess] at capTypeStrengthens
          cases capTypeStrengthens
          exact partialStrengthenTypedHcompPathOfSuccess
            modeIsUnivalent leftEndpoint rightEndpoint
            targetSidesPath targetCapValue carrierSuccess leftSuccess
            rightSuccess sidesPathRawStrengthens capRawStrengthens
            sidesPathRawRenames capRawRenames

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
    (_effectTagRenames :
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
    {targetCarrierA targetCarrierB : Ty level targetScope}
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
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
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
      have expectedForwardTypeStrengthens :
          (Ty.arrow carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.arrow targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.arrow = some (Ty.arrow targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedForwardTypeStrengthens] at forwardTypeStrengthens
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
                          exact partialStrengthenTypedEquivIntroHetOfSuccess
                            targetForward targetBackward targetLeftInv
                            targetRightInv carrierASuccess carrierBSuccess
                            forwardRawStrengthens backwardRawStrengthens
                            forwardRawRenames backwardRawRenames

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
  | @Term.var _ _ _ _ position =>
      match survives : strengthening.back position with
      | none => none
      | some targetPosition =>
          some
            (partialStrengthenTypedVarOfSurvives strengthening position
              targetPosition survives)
  | @Term.unit _ _ _ _ => by
      exact some (partialStrengthenTypedUnit strengthening)
  | @Term.lam _ _ _ _ domainType codomainType _ body =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match
                  partialStrengthenTyped? body
                    (strengthening :=
                      strengthening.lift domainType targetDomainType
                        domainSuccess) with
              | none => none
              | some bodyResult =>
                  some
                    (partialStrengthenTypedLam domainSuccess
                      codomainSuccess bodyResult)
  | @Term.app _ _ _ _ domainType codomainType _ _ functionTerm
      argumentTerm =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match functionRecurse :
                  partialStrengthenTyped? functionTerm
                    (strengthening := strengthening) with
              | none => none
              | some functionResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedApp domainSuccess
                          codomainSuccess functionResult argumentResult)
  | @Term.lamPi _ _ _ _ domainType _ _ body =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match
              partialStrengthenTyped? body
                (strengthening :=
                  strengthening.lift domainType targetDomainType
                    domainSuccess) with
          | none => none
          | some bodyResult =>
              some
                (partialStrengthenTypedLamPi domainSuccess bodyResult)
  | @Term.appPi _ _ _ _ domainType codomainType _ _ functionTerm
      argumentTerm =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetCodomainType =>
              match functionRecurse :
                  partialStrengthenTyped? functionTerm
                    (strengthening := strengthening) with
              | none => none
              | some functionResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedAppPi domainSuccess
                          codomainSuccess functionResult argumentResult)
  | @Term.pair _ _ _ _ _ secondType _ _ firstValue secondValue =>
      match secondTypeSuccess :
          secondType.partialStrengthen? strengthening.back.lift with
      | none => none
      | some targetSecondType =>
          match firstRecurse :
              partialStrengthenTyped? firstValue
                (strengthening := strengthening) with
          | none => none
          | some firstResult =>
              match secondRecurse :
                  partialStrengthenTyped? secondValue
                    (strengthening := strengthening) with
              | none => none
              | some secondResult =>
                  some
                    (partialStrengthenTypedPair secondTypeSuccess
                      firstResult secondResult)
  | @Term.fst _ _ _ _ firstType secondType _ pairTerm =>
      match firstSuccess :
          firstType.partialStrengthen? strengthening.back with
      | none => none
      | some targetFirstType =>
          match secondSuccess :
              secondType.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetSecondType =>
              match pairRecurse :
                  partialStrengthenTyped? pairTerm
                    (strengthening := strengthening) with
              | none => none
              | some pairResult =>
                  some
                    (partialStrengthenTypedFst firstSuccess secondSuccess
                      pairResult)
  | @Term.snd _ _ _ _ firstType secondType _ pairTerm =>
      match firstSuccess :
          firstType.partialStrengthen? strengthening.back with
      | none => none
      | some targetFirstType =>
          match secondSuccess :
              secondType.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetSecondType =>
              match pairRecurse :
                  partialStrengthenTyped? pairTerm
                    (strengthening := strengthening) with
              | none => none
              | some pairResult =>
                  some
                    (partialStrengthenTypedSnd firstSuccess secondSuccess
                      pairResult)
  | @Term.boolTrue _ _ _ _ => by
      exact some (partialStrengthenTypedBoolTrue strengthening)
  | @Term.boolFalse _ _ _ _ => by
      exact some (partialStrengthenTypedBoolFalse strengthening)
  | @Term.boolElim _ _ _ _ motiveType _ _ _ scrutinee thenBranch
      elseBranch =>
      match motiveSuccess :
          motiveType.partialStrengthen? strengthening.back.lift with
      | none => none
      | some targetMotiveType =>
          match scrutineeRecurse :
              partialStrengthenTyped? scrutinee
                (strengthening := strengthening) with
          | none => none
          | some scrutineeResult =>
              match thenRecurse :
                  partialStrengthenTyped? thenBranch
                    (strengthening := strengthening) with
              | none => none
              | some thenResult =>
                  match elseRecurse :
                      partialStrengthenTyped? elseBranch
                        (strengthening := strengthening) with
                  | none => none
                  | some elseResult =>
                      some
                        (partialStrengthenTypedBoolElim motiveSuccess
                          scrutineeResult thenResult elseResult)
  | @Term.natZero _ _ _ _ => by
      exact some (partialStrengthenTypedNatZero strengthening)
  | @Term.natSucc _ _ _ _ _ predecessor =>
      match predecessorRecurse :
          partialStrengthenTyped? predecessor
            (strengthening := strengthening) with
      | none => none
      | some predecessorResult =>
          some (partialStrengthenTypedNatSucc predecessorResult)
  | @Term.natElim _ _ _ _ _ _ _ _ scrutinee zeroBranch succBranch =>
      match scrutineeRecurse :
          partialStrengthenTyped? scrutinee
            (strengthening := strengthening) with
      | none => none
      | some scrutineeResult =>
          match zeroRecurse :
              partialStrengthenTyped? zeroBranch
                (strengthening := strengthening) with
          | none => none
          | some zeroResult =>
              match succRecurse :
                  partialStrengthenTyped? succBranch
                    (strengthening := strengthening) with
              | none => none
              | some succResult =>
                  some
                    (partialStrengthenTypedNatElim scrutineeResult
                      zeroResult succResult)
  | @Term.natRec _ _ _ _ _ _ _ _ scrutinee zeroBranch succBranch =>
      match scrutineeRecurse :
          partialStrengthenTyped? scrutinee
            (strengthening := strengthening) with
      | none => none
      | some scrutineeResult =>
          match zeroRecurse :
              partialStrengthenTyped? zeroBranch
                (strengthening := strengthening) with
          | none => none
          | some zeroResult =>
              match succRecurse :
                  partialStrengthenTyped? succBranch
                    (strengthening := strengthening) with
              | none => none
              | some succResult =>
                  some
                    (partialStrengthenTypedNatRec scrutineeResult
                      zeroResult succResult)
  | @Term.listNil _ _ _ _ elementType =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          some
            (partialStrengthenTypedListNilOfType strengthening
              elementType targetElementType elementSuccess)
  | @Term.listCons _ _ _ _ _ _ _ headTerm tailTerm =>
      match headRecurse :
          partialStrengthenTyped? headTerm
            (strengthening := strengthening) with
      | none => none
      | some headResult =>
          match tailRecurse :
              partialStrengthenTyped? tailTerm
                (strengthening := strengthening) with
          | none => none
          | some tailResult =>
              some (partialStrengthenTypedListCons headResult tailResult)
  | @Term.listElim _ _ _ _ elementType _ _ _ _ scrutinee nilBranch
      consBranch =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          match scrutineeRecurse :
              partialStrengthenTyped? scrutinee
                (strengthening := strengthening) with
          | none => none
          | some scrutineeResult =>
              match nilRecurse :
                  partialStrengthenTyped? nilBranch
                    (strengthening := strengthening) with
              | none => none
              | some nilResult =>
                  match consRecurse :
                      partialStrengthenTyped? consBranch
                        (strengthening := strengthening) with
                  | none => none
                  | some consResult =>
                      some
                        (partialStrengthenTypedListElim elementSuccess
                          scrutineeResult nilResult consResult)
  | @Term.optionNone _ _ _ _ elementType =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          some
            (partialStrengthenTypedOptionNoneOfType strengthening
              elementType targetElementType elementSuccess)
  | @Term.optionSome _ _ _ _ _ _ valueTerm =>
      match valueRecurse :
          partialStrengthenTyped? valueTerm
            (strengthening := strengthening) with
      | none => none
      | some valueResult =>
          some (partialStrengthenTypedOptionSome valueResult)
  | @Term.optionMatch _ _ _ _ elementType _ _ _ _ scrutinee noneBranch
      someBranch =>
      match elementSuccess :
          elementType.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementType =>
          match scrutineeRecurse :
              partialStrengthenTyped? scrutinee
                (strengthening := strengthening) with
          | none => none
          | some scrutineeResult =>
              match noneRecurse :
                  partialStrengthenTyped? noneBranch
                    (strengthening := strengthening) with
              | none => none
              | some noneResult =>
                  match someRecurse :
                      partialStrengthenTyped? someBranch
                        (strengthening := strengthening) with
                  | none => none
                  | some someResult =>
                      some
                        (partialStrengthenTypedOptionMatch elementSuccess
                          scrutineeResult noneResult someResult)
  | @Term.eitherInl _ _ _ _ _ rightType _ valueTerm =>
      match rightSuccess :
          rightType.partialStrengthen? strengthening.back with
      | none => none
      | some targetRightType =>
          match valueRecurse :
              partialStrengthenTyped? valueTerm
                (strengthening := strengthening) with
          | none => none
          | some valueResult =>
              some
                (partialStrengthenTypedEitherInlOfRightType
                  rightSuccess valueResult)
  | @Term.eitherInr _ _ _ _ leftType _ _ valueTerm =>
      match leftSuccess :
          leftType.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftType =>
          match valueRecurse :
              partialStrengthenTyped? valueTerm
                (strengthening := strengthening) with
          | none => none
          | some valueResult =>
              some
                (partialStrengthenTypedEitherInrOfLeftType
                  leftSuccess valueResult)
  | @Term.eitherMatch _ _ _ _ leftType rightType motiveType _ _ _ scrutinee
      leftBranch rightBranch =>
      match leftSuccess :
          leftType.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftType =>
          match rightSuccess :
              rightType.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightType =>
              match motiveSuccess :
                  motiveType.partialStrengthen? strengthening.back with
              | none => none
              | some targetMotiveType =>
                  match scrutineeRecurse :
                      partialStrengthenTyped? scrutinee
                        (strengthening := strengthening) with
                  | none => none
                  | some scrutineeResult =>
                      match leftRecurse :
                          partialStrengthenTyped? leftBranch
                            (strengthening := strengthening) with
                      | none => none
                      | some leftResult =>
                          match rightRecurse :
                              partialStrengthenTyped? rightBranch
                                (strengthening := strengthening) with
                          | none => none
                          | some rightResult =>
                              some
                                (partialStrengthenTypedEitherMatch leftSuccess
                                  rightSuccess motiveSuccess scrutineeResult
                                  leftResult rightResult)
  | @Term.refl _ _ _ _ carrier rawWitness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetWitness =>
              some (partialStrengthenTypedRefl carrierSuccess witnessSuccess)
  | @Term.idJ _ _ _ _ carrier leftEndpoint rightEndpoint _ _ _ baseCase
      witness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match baseRecurse :
                      partialStrengthenTyped? baseCase
                        (strengthening := strengthening) with
                  | none => none
                  | some baseResult =>
                      match witnessRecurse :
                          partialStrengthenTyped? witness
                            (strengthening := strengthening) with
                      | none => none
                      | some witnessResult =>
                          some
                            (partialStrengthenTypedIdJ carrierSuccess
                              leftSuccess rightSuccess baseResult
                              witnessResult)
  | @Term.oeqRefl _ _ _ _ carrier rawWitness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetWitness =>
              some
                (partialStrengthenTypedOeqRefl carrierSuccess witnessSuccess)
  | @Term.oeqJ _ _ _ _ carrier leftEndpoint rightEndpoint _ _ _ baseCase
      witness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match baseRecurse :
                      partialStrengthenTyped? baseCase
                        (strengthening := strengthening) with
                  | none => none
                  | some baseResult =>
                      match witnessRecurse :
                          partialStrengthenTyped? witness
                            (strengthening := strengthening) with
                      | none => none
                      | some witnessResult =>
                          some
                            (partialStrengthenTypedOeqJ carrierSuccess
                              leftSuccess rightSuccess baseResult
                              witnessResult)
  | @Term.oeqFunext _ _ _ _ domainType codomainType leftFunctionRaw
      rightFunctionRaw _ pointwiseProof =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match leftSuccess :
                  leftFunctionRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetLeftFunctionRaw =>
                  match rightSuccess :
                      rightFunctionRaw.partialStrengthen?
                        strengthening.back with
                  | none => none
                  | some targetRightFunctionRaw =>
                      match pointwiseRecurse :
                          partialStrengthenTyped? pointwiseProof
                            (strengthening := strengthening) with
                      | none => none
                      | some pointwiseResult =>
                          some
                            (partialStrengthenTypedOeqFunext domainType
                              codomainType targetDomainType
                              targetCodomainType leftFunctionRaw
                              rightFunctionRaw targetLeftFunctionRaw
                              targetRightFunctionRaw domainSuccess
                              codomainSuccess leftSuccess rightSuccess
                              pointwiseResult)
  | @Term.idStrictRefl _ _ _ _ modeIsStrict carrier rawWitness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match witnessSuccess :
              rawWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetWitness =>
              some
                (partialStrengthenTypedIdStrictRefl modeIsStrict
                  carrierSuccess witnessSuccess)
  | @Term.idStrictRec _ _ _ _ modeIsStrict carrier leftEndpoint
      rightEndpoint _ _ _ baseCase witness =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match baseRecurse :
                      partialStrengthenTyped? baseCase
                        (strengthening := strengthening) with
                  | none => none
                  | some baseResult =>
                      match witnessRecurse :
                          partialStrengthenTyped? witness
                            (strengthening := strengthening) with
                      | none => none
                      | some witnessResult =>
                          some
                            (partialStrengthenTypedIdStrictRec modeIsStrict
                              carrierSuccess leftSuccess rightSuccess
                              baseResult witnessResult)
  | @Term.modIntro _ _ _ _ _ _ innerTerm =>
      match innerRecurse :
          partialStrengthenTyped? innerTerm
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedModIntro innerResult)
  | @Term.modElim _ _ _ _ _ _ innerTerm =>
      match innerRecurse :
          partialStrengthenTyped? innerTerm
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedModElim innerResult)
  | @Term.subsume _ _ _ _ _ _ innerTerm =>
      match innerRecurse :
          partialStrengthenTyped? innerTerm
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedSubsume innerResult)
  | @Term.interval0 _ _ _ _ => by
      exact some (partialStrengthenTypedInterval0 strengthening)
  | @Term.interval1 _ _ _ _ => by
      exact some (partialStrengthenTypedInterval1 strengthening)
  | @Term.intervalOpp _ _ _ _ _ innerValue =>
      match innerRecurse :
          partialStrengthenTyped? innerValue
            (strengthening := strengthening) with
      | none => none
      | some innerResult =>
          some (partialStrengthenTypedIntervalOpp innerResult)
  | @Term.intervalMeet _ _ _ _ _ _ leftValue rightValue =>
      match leftRecurse :
          partialStrengthenTyped? leftValue
            (strengthening := strengthening) with
      | none => none
      | some leftResult =>
          match rightRecurse :
              partialStrengthenTyped? rightValue
                (strengthening := strengthening) with
          | none => none
          | some rightResult =>
              some (partialStrengthenTypedIntervalMeet leftResult rightResult)
  | @Term.intervalJoin _ _ _ _ _ _ leftValue rightValue =>
      match leftRecurse :
          partialStrengthenTyped? leftValue
            (strengthening := strengthening) with
      | none => none
      | some leftResult =>
          match rightRecurse :
              partialStrengthenTyped? rightValue
                (strengthening := strengthening) with
          | none => none
          | some rightResult =>
              some (partialStrengthenTypedIntervalJoin leftResult rightResult)
  | @Term.pathLam _ _ _ _ modeIsUnivalent carrierType leftEndpoint
      rightEndpoint _ body =>
      match carrierSuccess :
          carrierType.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrierType =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match partialStrengthenTyped? body
                      (strengthening :=
                        strengthening.lift Ty.interval Ty.interval rfl) with
                  | none => none
                  | some bodyResult =>
                      some
                        (partialStrengthenTypedPathLam modeIsUnivalent
                          carrierSuccess leftSuccess rightSuccess bodyResult)
  | @Term.pathApp _ _ _ _ modeIsUnivalent carrierType leftEndpoint
      rightEndpoint _ _ pathTerm intervalTerm =>
      match carrierSuccess :
          carrierType.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrierType =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftEndpoint =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightEndpoint =>
                  match pathRecurse :
                      partialStrengthenTyped? pathTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some pathResult =>
                      match intervalRecurse :
                          partialStrengthenTyped? intervalTerm
                            (strengthening := strengthening) with
                      | none => none
                      | some intervalResult =>
                          some
                            (partialStrengthenTypedPathApp modeIsUnivalent
                              carrierSuccess leftSuccess rightSuccess
                              pathResult intervalResult)
  | @Term.glueIntro _ _ _ _ modeIsUnivalent baseType boundaryWitness _ _
      baseValue partialValue =>
      match baseTypeSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => none
      | some targetBaseType =>
          match boundarySuccess :
              boundaryWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetBoundaryWitness =>
              match partialStrengthenTyped? baseValue
                  (strengthening := strengthening) with
              | none => none
              | some baseResult =>
                  match partialStrengthenTyped? partialValue
                      (strengthening := strengthening) with
                  | none => none
                  | some partialResult =>
                      some
                        (partialStrengthenTypedGlueIntro modeIsUnivalent
                          baseType targetBaseType boundaryWitness
                          targetBoundaryWitness baseTypeSuccess
                          boundarySuccess baseResult partialResult)
  | @Term.glueElim _ _ _ _ modeIsUnivalent baseType boundaryWitness _
      gluedValue =>
      match baseSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => none
      | some targetBaseType =>
          match boundarySuccess :
              boundaryWitness.partialStrengthen? strengthening.back with
          | none => none
          | some targetBoundaryWitness =>
              match gluedRecurse :
                  partialStrengthenTyped? gluedValue
                    (strengthening := strengthening) with
              | none => none
              | some gluedResult =>
                  some
                    (partialStrengthenTypedGlueElim modeIsUnivalent
                      baseSuccess boundarySuccess gluedResult)
  | @Term.transp _ _ _ _ modeIsUnivalent universeLevel universeLevelLt
      sourceType targetType sourceTypeRaw targetTypeRaw _ _ typePath
      sourceValue =>
      match sourceTypeSuccess :
          sourceType.partialStrengthen? strengthening.back with
      | none => none
      | some targetSourceType =>
          match targetTypeSuccess :
              targetType.partialStrengthen? strengthening.back with
          | none => none
          | some targetTargetType =>
              match sourceTypeRawSuccess :
                  sourceTypeRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetSourceTypeRaw =>
                  match targetTypeRawSuccess :
                      targetTypeRaw.partialStrengthen? strengthening.back with
                  | none => none
                  | some targetTargetTypeRaw =>
                      match pathRecurse :
                          partialStrengthenTyped? typePath
                            (strengthening := strengthening) with
                      | none => none
                      | some pathResult =>
                          match sourceRecurse :
                              partialStrengthenTyped? sourceValue
                                (strengthening := strengthening) with
                          | none => none
                          | some sourceResult =>
                              some
                                (partialStrengthenTypedTransp
                                  modeIsUnivalent universeLevel
                                  universeLevelLt sourceType targetType
                                  targetSourceType targetTargetType
                                  sourceTypeRaw targetTypeRaw
                                  targetSourceTypeRaw targetTargetTypeRaw
                                  sourceTypeSuccess targetTypeSuccess
                                  sourceTypeRawSuccess targetTypeRawSuccess
                                  pathResult sourceResult)
  | @Term.hcomp _ _ _ _ modeIsUnivalent _ _ _ sidesValue capValue =>
      match sidesRecurse :
          partialStrengthenTyped? sidesValue
            (strengthening := strengthening) with
      | none => none
      | some sidesResult =>
          match capRecurse :
              partialStrengthenTyped? capValue
                (strengthening := strengthening) with
          | none => none
          | some capResult =>
              some
                (partialStrengthenTypedHcomp modeIsUnivalent sidesResult
                  capResult)
  | @Term.hcompPath _ _ _ _ modeIsUnivalent carrierType leftEndpoint
      rightEndpoint _ _ sidesPath capValue =>
      match carrierSuccess :
          carrierType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match leftSuccess :
              leftEndpoint.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match rightSuccess :
                  rightEndpoint.partialStrengthen? strengthening.back with
              | none => none
              | some _ =>
                  match sidesRecurse :
                      partialStrengthenTyped? sidesPath
                        (strengthening := strengthening) with
                  | none => none
                  | some sidesResult =>
                      match capRecurse :
                          partialStrengthenTyped? capValue
                            (strengthening := strengthening) with
                      | none => none
                      | some capResult =>
                          some
                            (partialStrengthenTypedHcompPath modeIsUnivalent
                              leftEndpoint rightEndpoint carrierSuccess
                              leftSuccess rightSuccess sidesResult capResult)
  | @Term.recordIntro _ _ _ _ _ _ firstField =>
      match fieldRecurse :
          partialStrengthenTyped? firstField
            (strengthening := strengthening) with
      | none => none
      | some fieldResult =>
          some (partialStrengthenTypedRecordIntro fieldResult)
  | @Term.recordProj _ _ _ _ singleFieldType _ recordValue =>
      match fieldSuccess :
          singleFieldType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match recordRecurse :
              partialStrengthenTyped? recordValue
                (strengthening := strengthening) with
          | none => none
          | some recordResult =>
              some
                (partialStrengthenTypedRecordProj fieldSuccess recordResult)
  | @Term.refineIntro _ _ _ _ _ predicate _ _ baseValue predicateProof =>
      match predicateSuccess :
          predicate.partialStrengthen? strengthening.back.lift with
      | none => none
      | some _ =>
          match baseRecurse :
              partialStrengthenTyped? baseValue
                (strengthening := strengthening) with
          | none => none
          | some baseResult =>
              match proofRecurse :
                  partialStrengthenTyped? predicateProof
                    (strengthening := strengthening) with
              | none => none
              | some proofResult =>
                  some
                    (partialStrengthenTypedRefineIntro predicateSuccess
                      baseResult proofResult)
  | @Term.refineElim _ _ _ _ baseType predicate _ refinedValue =>
      match baseSuccess :
          baseType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match predicateSuccess :
              predicate.partialStrengthen? strengthening.back.lift with
          | none => none
          | some _ =>
              match refinedRecurse :
                  partialStrengthenTyped? refinedValue
                    (strengthening := strengthening) with
              | none => none
              | some refinedResult =>
                  some
                    (partialStrengthenTypedRefineElim baseSuccess
                      predicateSuccess refinedResult)
  | @Term.codataUnfold _ _ _ _ _ outputType _ _ initialState transition =>
      match outputSuccess :
          outputType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match stateRecurse :
              partialStrengthenTyped? initialState
                (strengthening := strengthening) with
          | none => none
          | some stateResult =>
              match transitionRecurse :
                  partialStrengthenTyped? transition
                    (strengthening := strengthening) with
              | none => none
              | some transitionResult =>
                  some
                    (partialStrengthenTypedCodataUnfold outputSuccess
                      stateResult transitionResult)
  | @Term.codataDest _ _ _ _ stateType outputType _ codataValue =>
      match stateSuccess :
          stateType.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match outputSuccess :
              outputType.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match codataRecurse :
                  partialStrengthenTyped? codataValue
                    (strengthening := strengthening) with
              | none => none
              | some codataResult =>
                  some
                    (partialStrengthenTypedCodataDest stateSuccess
                      outputSuccess codataResult)
  | @Term.sessionSend _ _ _ _ protocolStep _ _ _ channel payload =>
      match protocolSuccess :
          protocolStep.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match channelRecurse :
              partialStrengthenTyped? channel
                (strengthening := strengthening) with
          | none => none
          | some channelResult =>
              match payloadRecurse :
                  partialStrengthenTyped? payload
                    (strengthening := strengthening) with
              | none => none
              | some payloadResult =>
                  some
                    (partialStrengthenTypedSessionSend protocolSuccess
                      channelResult payloadResult)
  | @Term.sessionRecv _ _ _ _ protocolStep _ channel =>
      match protocolSuccess :
          protocolStep.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match channelRecurse :
              partialStrengthenTyped? channel
                (strengthening := strengthening) with
          | none => none
          | some channelResult =>
              some
                (partialStrengthenTypedSessionRecv protocolSuccess
                  channelResult)
  | @Term.effectPerform _ _ _ _ effectTag effectRow operationSignature
      canPerformOperation _ _ operationTag arguments =>
      match effectTagSuccess :
          effectTag.partialStrengthen? strengthening.back with
      | none => none
      | some targetEffectTag =>
          match argumentCarrierSuccess :
              operationSignature.argumentCarrier.partialStrengthen?
                strengthening.back with
          | none => none
          | some targetArgumentCarrier =>
              match resultCarrierSuccess :
                  operationSignature.resultCarrier.partialStrengthen?
                    strengthening.back with
              | none => none
              | some targetResultCarrier =>
                  match partialStrengthenTyped? operationTag
                      (strengthening := strengthening) with
                  | none => none
                  | some operationResult =>
                      match partialStrengthenTyped? arguments
                          (strengthening := strengthening) with
                      | none => none
                      | some argumentsResult =>
                          some
                            (partialStrengthenTypedEffectPerform effectTag
                              targetEffectTag effectRow operationSignature
                              targetArgumentCarrier targetResultCarrier
                              canPerformOperation effectTagSuccess
                              argumentCarrierSuccess resultCarrierSuccess
                              operationResult argumentsResult)
  | @Term.universeCode _ _ _ _ innerLevel outerLevel cumulOk levelLe =>
      some
        (partialStrengthenTypedUniverseCode strengthening innerLevel
          outerLevel cumulOk levelLe)
  | @Term.cumulUp _ _ _ _ lowerLevel higherLevel cumulMonotone levelLeLow
      levelLeHigh _ typeCode =>
      match codeRecurse :
          partialStrengthenTyped? typeCode
            (strengthening := strengthening) with
      | none => none
      | some codeResult =>
          some
            (partialStrengthenTypedCumulUp lowerLevel higherLevel
              cumulMonotone levelLeLow levelLeHigh codeResult)
  | @Term.equivReflId _ _ _ _ carrier =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          some
            (partialStrengthenTypedEquivReflId carrier targetCarrier
              carrierSuccess)
  | @Term.funextRefl _ _ _ _ domainType codomainType applyRaw =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match applySuccess :
                  applyRaw.partialStrengthen? strengthening.back.lift with
              | none => none
              | some targetApplyRaw =>
                  some
                    (partialStrengthenTypedFunextRefl domainType
                      codomainType targetDomainType targetCodomainType
                      applyRaw targetApplyRaw domainSuccess
                      codomainSuccess applySuccess)
  | @Term.equivReflIdAtId _ _ _ _ innerLevel innerLevelLt carrier
      carrierRaw =>
      match carrierSuccess :
          carrier.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrier =>
          match carrierRawSuccess :
              carrierRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetCarrierRaw =>
              some
                (partialStrengthenTypedEquivReflIdAtId innerLevel
                  innerLevelLt carrier targetCarrier carrierRaw
                  targetCarrierRaw carrierSuccess carrierRawSuccess)
  | @Term.funextReflAtId _ _ _ _ domainType codomainType applyRaw =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match applySuccess :
                  applyRaw.partialStrengthen? strengthening.back.lift with
              | none => none
              | some targetApplyRaw =>
                  some
                    (partialStrengthenTypedFunextReflAtId domainType
                      codomainType targetDomainType targetCodomainType
                      applyRaw targetApplyRaw domainSuccess
                      codomainSuccess applySuccess)
  | @Term.equivIntroHet _ _ _ _ carrierA carrierB _ _ _ _ forward backward
      leftInv rightInv =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match forwardRecurse :
                  partialStrengthenTyped? forward
                    (strengthening := strengthening) with
              | none => none
              | some forwardResult =>
                  match backwardRecurse :
                      partialStrengthenTyped? backward
                        (strengthening := strengthening) with
                  | none => none
                  | some backwardResult =>
                      match leftInvRecurse :
                          partialStrengthenTyped? leftInv
                            (strengthening := strengthening) with
                      | none => none
                      | some leftInvResult =>
                          match rightInvRecurse :
                              partialStrengthenTyped? rightInv
                                (strengthening := strengthening) with
                          | none => none
                          | some rightInvResult =>
                              some
                                (partialStrengthenTypedEquivIntroHet
                                  carrierASuccess carrierBSuccess
                                  forwardResult backwardResult leftInvResult
                                  rightInvResult)
  | @Term.equivApp _ _ _ _ carrierA carrierB _ _ equivTerm argumentTerm =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match equivRecurse :
                  partialStrengthenTyped? equivTerm
                    (strengthening := strengthening) with
              | none => none
              | some equivResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedEquivApp carrierASuccess
                          carrierBSuccess equivResult argumentResult)
  | @Term.uaIntroHet _ _ _ _ innerLevel innerLevelLt carrierA carrierB
      carrierARaw carrierBRaw forwardRaw backwardRaw equivWitness =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some targetCarrierA =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some targetCarrierB =>
              match carrierARawSuccess :
                  carrierARaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetCarrierARaw =>
                  match carrierBRawSuccess :
                      carrierBRaw.partialStrengthen? strengthening.back with
                  | none => none
                  | some targetCarrierBRaw =>
                      match forwardRawSuccess :
                          forwardRaw.partialStrengthen?
                            strengthening.back with
                      | none => none
                      | some targetForwardRaw =>
                          match backwardRawSuccess :
                              backwardRaw.partialStrengthen?
                                strengthening.back with
                          | none => none
                          | some targetBackwardRaw =>
                              match equivRecurse :
                                  partialStrengthenTyped? equivWitness
                                    (strengthening := strengthening) with
                              | none => none
                              | some equivResult =>
                                  some
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
      applyBRaw =>
      match domainSuccess :
          domainType.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainType =>
          match codomainSuccess :
              codomainType.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainType =>
              match applyASuccess :
                  applyARaw.partialStrengthen? strengthening.back.lift with
              | none => none
              | some targetApplyARaw =>
                  match applyBSuccess :
                      applyBRaw.partialStrengthen? strengthening.back.lift with
                  | none => none
                  | some targetApplyBRaw =>
                      some
                        (partialStrengthenTypedFunextIntroHet domainType
                          codomainType targetDomainType targetCodomainType
                          applyARaw applyBRaw targetApplyARaw
                          targetApplyBRaw domainSuccess codomainSuccess
                          applyASuccess applyBSuccess)
  | @Term.arrowCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw =>
      match domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainCodeRaw =>
          match codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetCodomainCodeRaw =>
              some
                (partialStrengthenTypedArrowCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.piTyCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw =>
      match domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainCodeRaw =>
          match codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetCodomainCodeRaw =>
              some
                (partialStrengthenTypedPiTyCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.sigmaTyCode _ _ _ _ outerLevel levelLe domainCodeRaw
      codomainCodeRaw =>
      match domainSuccess :
          domainCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetDomainCodeRaw =>
          match codomainSuccess :
              codomainCodeRaw.partialStrengthen? strengthening.back.lift with
          | none => none
          | some targetCodomainCodeRaw =>
              some
                (partialStrengthenTypedSigmaTyCode outerLevel levelLe
                  domainCodeRaw codomainCodeRaw targetDomainCodeRaw
                  targetCodomainCodeRaw domainSuccess codomainSuccess)
  | @Term.productCode _ _ _ _ outerLevel levelLe firstCodeRaw
      secondCodeRaw =>
      match firstSuccess :
          firstCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetFirstCodeRaw =>
          match secondSuccess :
              secondCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetSecondCodeRaw =>
              some
                (partialStrengthenTypedProductCode outerLevel levelLe
                  firstCodeRaw secondCodeRaw targetFirstCodeRaw
                  targetSecondCodeRaw firstSuccess secondSuccess)
  | @Term.sumCode _ _ _ _ outerLevel levelLe leftCodeRaw rightCodeRaw =>
      match leftSuccess :
          leftCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftCodeRaw =>
          match rightSuccess :
              rightCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightCodeRaw =>
              some
                (partialStrengthenTypedSumCode outerLevel levelLe
                  leftCodeRaw rightCodeRaw targetLeftCodeRaw
                  targetRightCodeRaw leftSuccess rightSuccess)
  | @Term.listCode _ _ _ _ outerLevel levelLe elementCodeRaw =>
      match elementSuccess :
          elementCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementCodeRaw =>
          some
            (partialStrengthenTypedListCode outerLevel levelLe
              elementCodeRaw targetElementCodeRaw elementSuccess)
  | @Term.optionCode _ _ _ _ outerLevel levelLe elementCodeRaw =>
      match elementSuccess :
          elementCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetElementCodeRaw =>
          some
            (partialStrengthenTypedOptionCode outerLevel levelLe
              elementCodeRaw targetElementCodeRaw elementSuccess)
  | @Term.eitherCode _ _ _ _ outerLevel levelLe leftCodeRaw rightCodeRaw =>
      match leftSuccess :
          leftCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftCodeRaw =>
          match rightSuccess :
              rightCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightCodeRaw =>
              some
                (partialStrengthenTypedEitherCode outerLevel levelLe
                  leftCodeRaw rightCodeRaw targetLeftCodeRaw
                  targetRightCodeRaw leftSuccess rightSuccess)
  | @Term.idCode _ _ _ _ outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      match typeSuccess :
          typeCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetTypeCodeRaw =>
          match leftSuccess :
              leftRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetLeftRaw =>
              match rightSuccess :
                  rightRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetRightRaw =>
                  some
                    (partialStrengthenTypedIdCode outerLevel levelLe
                      typeCodeRaw leftRaw rightRaw targetTypeCodeRaw
                      targetLeftRaw targetRightRaw typeSuccess leftSuccess
                      rightSuccess)
  | @Term.equivCode _ _ _ _ outerLevel levelLe leftTypeCodeRaw
      rightTypeCodeRaw =>
      match leftSuccess :
          leftTypeCodeRaw.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftTypeCodeRaw =>
          match rightSuccess :
              rightTypeCodeRaw.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightTypeCodeRaw =>
              some
                (partialStrengthenTypedEquivCode outerLevel levelLe
                  leftTypeCodeRaw rightTypeCodeRaw targetLeftTypeCodeRaw
                  targetRightTypeCodeRaw leftSuccess rightSuccess)
  | @Term.uaToEquiv _ _ _ _ innerLevel innerLevelLt leftTy rightTy
      leftTyRaw rightTyRaw _ proof =>
      match leftTySuccess :
          leftTy.partialStrengthen? strengthening.back with
      | none => none
      | some targetLeftTy =>
          match rightTySuccess :
              rightTy.partialStrengthen? strengthening.back with
          | none => none
          | some targetRightTy =>
              match leftRawSuccess :
                  leftTyRaw.partialStrengthen? strengthening.back with
              | none => none
              | some targetLeftTyRaw =>
                  match rightRawSuccess :
                      rightTyRaw.partialStrengthen? strengthening.back with
                  | none => none
                  | some targetRightTyRaw =>
                      match proofRecurse :
                          partialStrengthenTyped? proof
                            (strengthening := strengthening) with
                      | none => none
                      | some proofResult =>
                          some
                            (partialStrengthenTypedUaToEquiv innerLevel
                              innerLevelLt leftTy rightTy targetLeftTy
                              targetRightTy leftTyRaw rightTyRaw
                              targetLeftTyRaw targetRightTyRaw
                              leftTySuccess rightTySuccess leftRawSuccess
                              rightRawSuccess proofResult)
  | @Term.equivApply _ _ _ _ carrierA carrierB _ _ equivTerm argumentTerm =>
      match carrierASuccess :
          carrierA.partialStrengthen? strengthening.back with
      | none => none
      | some _ =>
          match carrierBSuccess :
              carrierB.partialStrengthen? strengthening.back with
          | none => none
          | some _ =>
              match equivRecurse :
                  partialStrengthenTyped? equivTerm
                    (strengthening := strengthening) with
              | none => none
              | some equivResult =>
                  match argumentRecurse :
                      partialStrengthenTyped? argumentTerm
                        (strengthening := strengthening) with
                  | none => none
                  | some argumentResult =>
                      some
                        (partialStrengthenTypedEquivApply carrierASuccess
                          carrierBSuccess equivResult argumentResult)

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

/-- Canonical `StrengtheningResult` for the rename-image case.

Given an injective renaming `forwardRename : RawRenaming sourceScope
targetScope` with typed companion `typedRenaming`, a partial inverse
`renameInverse`, and an original typed term `original` living in the
source context, build the canonical `StrengtheningResult` for
`Term.rename typedRenaming original` (which lives in the target
context) through the `ContextStrengthening.ofRenaming`-induced
strengthening (which goes back from target to source).

Mechanical content:
* `targetType := originalTy` — the strengthening recovers the original
  type.
* `targetRaw := originalRaw` — analogous at the raw layer.
* `targetTerm := original` — the original typed term itself.
* `typeStrengthens` — discharges via `Ty.partialStrengthen?_rename_some`
  applied at `targetRenaming := RawRenaming.identity`, then closed via
  `Ty.rename_identity`.
* `rawStrengthens` — analogous at raw, via
  `RawTerm.partialStrengthen?_rename_some` + `RawTerm.rename_identity`.
* `typeRenames` / `rawRenames` — both `rfl` because the
  `ContextStrengthening.ofRenaming`'s `forward` field IS `forwardRename`
  by definition.

This is the canonical witness consumed by strength-T1
(`Term.strengthenTyped?_rename_eq`): the headline asserts that the
dispatcher produces exactly this StrengtheningResult on a renamed
input. -/
def StrengtheningResult.fromRename
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {originalTy : Ty level sourceScope}
    {originalRaw : RawTerm sourceScope}
    (original : Term sourceCtx originalTy originalRaw) :
    StrengtheningResult
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)
      (Term.rename typedRenaming original) where
  targetType := originalTy
  targetRaw := originalRaw
  targetTerm := original
  typeStrengthens := by
    show (originalTy.rename forwardRename).partialStrengthen? renameInverse =
      some originalTy
    rw [Ty.partialStrengthen?_rename_some originalTy forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity originalTy]
  rawStrengthens := by
    show (originalRaw.rename forwardRename).partialStrengthen? renameInverse =
      some originalRaw
    rw [RawTerm.partialStrengthen?_rename_some originalRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity originalRaw]
  typeRenames := rfl
  rawRenames := rfl

/-! ## strength-T1: per-ctor renaming-image dispatcher equations.

For each Term constructor, the dispatcher `partialStrengthenTyped?`
applied to the renamed term through the `ContextStrengthening.ofRenaming`-
induced strengthening produces exactly the canonical `StrengtheningResult`
recovering the original.

These per-ctor lemmas compose into the full strength-T1 universal
headline `Term.strengthenTyped?_rename_eq` (78-case structural
induction).  This block starts the closed-atomic family (unit /
boolTrue / boolFalse / natZero / interval0 / interval1 /
universeCode) and the var case; recursive ctors land in follow-up
ticks. -/

/-- Closed-atomic strength-T1 case: `Term.unit`.

The dispatcher's unit arm returns `partialStrengthenTypedUnit`
which produces a `StrengtheningResult` with `targetTerm := Term.unit`
in the strengthening's target context.  The `fromRename` constructor
for the unit original also produces a `StrengtheningResult` whose
fields match.  Both StrengtheningResults are definitionally equal by
field eta. -/
theorem strengthenTyped?_rename_eq_unit
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.unit (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.unit (context := sourceCtx))) := rfl

/-- Closed-atomic strength-T1 case: `Term.boolTrue`. -/
theorem strengthenTyped?_rename_eq_boolTrue
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.boolTrue (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.boolTrue (context := sourceCtx))) := rfl

/-- Closed-atomic strength-T1 case: `Term.boolFalse`. -/
theorem strengthenTyped?_rename_eq_boolFalse
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.boolFalse (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.boolFalse (context := sourceCtx))) := rfl

/-- Closed-atomic strength-T1 case: `Term.natZero`. -/
theorem strengthenTyped?_rename_eq_natZero
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.natZero (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.natZero (context := sourceCtx))) := rfl

/-- Closed-atomic strength-T1 case: `Term.interval0`. -/
theorem strengthenTyped?_rename_eq_interval0
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.interval0 (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.interval0 (context := sourceCtx))) := rfl

/-- Closed-atomic strength-T1 case: `Term.interval1`. -/
theorem strengthenTyped?_rename_eq_interval1
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.interval1 (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.interval1 (context := sourceCtx))) := rfl

/-- Parametric-atomic strength-T1 case: `Term.universeCode`.

Carries value-level data (innerLevel, outerLevel, cumulOk, levelLe)
but no Term children.  The Term.rename arm produces another
universeCode with the same value-level fields, and the dispatcher
matches the universeCode arm directly. -/
theorem strengthenTyped?_rename_eq_universeCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.universeCode (context := sourceCtx) innerLevel outerLevel
            cumulOk levelLe))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.universeCode (context := sourceCtx) innerLevel outerLevel
            cumulOk levelLe)) := rfl

/-- Parametric-atomic strength-T1 case: `Term.listNil`.

Single-Ty payload (`elementType`).  Dispatcher's elementType match is
unblocked by `subst`-ing the propositional witness `targetElementType =
elementType` derived from `Ty.partialStrengthen?_rename_some`. -/
theorem strengthenTyped?_rename_eq_listNil
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {elementType : Ty level sourceScope} :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listNil (context := sourceCtx) (elementType := elementType)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.listNil (context := sourceCtx)
            (elementType := elementType))) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse
        = some elementType := by
    rw [Ty.partialStrengthen?_rename_some elementType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity elementType]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementType elementSuccess =>
    have witnessEq : targetElementType = elementType :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst witnessEq
    rfl

/-- Parametric-atomic strength-T1 case: `Term.optionNone`.

Mirror of `listNil`: single Ty payload, subst-via-witness pattern. -/
theorem strengthenTyped?_rename_eq_optionNone
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {elementType : Ty level sourceScope} :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionNone (context := sourceCtx) (elementType := elementType)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.optionNone (context := sourceCtx)
            (elementType := elementType))) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse
        = some elementType := by
    rw [Ty.partialStrengthen?_rename_some elementType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity elementType]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementType elementSuccess =>
    have witnessEq : targetElementType = elementType :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst witnessEq
    rfl

/-- Parametric-atomic strength-T1 case: `Term.equivReflId`.

Single Ty payload (carrier).  Subst-via-witness pattern. -/
theorem strengthenTyped?_rename_eq_equivReflId
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {carrier : Ty level sourceScope} :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivReflId (context := sourceCtx) carrier))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivReflId (context := sourceCtx) carrier)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have witnessEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst witnessEq
    rfl

/-- Parametric-atomic strength-T1 case: `Term.refl`.

Two-payload (carrier Ty + rawWitness RawTerm).  Sequence two subst-
via-witness steps; the outer `split` exposes the carrier match, the
inner `split` exposes the witness match. -/
theorem strengthenTyped?_rename_eq_refl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refl (context := sourceCtx) carrier rawWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.refl (context := sourceCtx) carrier rawWitness)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have witnessStrengthens :
      (rawWitness.rename forwardRename).partialStrengthen? renameInverse
        = some rawWitness := by
    rw [RawTerm.partialStrengthen?_rename_some rawWitness forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rawWitness]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noWitnessSuccess =>
      exact absurd (witnessStrengthens.symm.trans noWitnessSuccess)
        (by intro contra; cases contra)
    next targetWitness witnessSuccess =>
      have witnessEq : targetWitness = rawWitness :=
        Option.some.inj (witnessSuccess.symm.trans witnessStrengthens)
      subst witnessEq
      rfl

/-- Parametric-atomic strength-T1 case: `Term.oeqRefl`.

Same Ty + RawTerm two-payload shape as `refl`. -/
theorem strengthenTyped?_rename_eq_oeqRefl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.oeqRefl (context := sourceCtx) carrier rawWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.oeqRefl (context := sourceCtx) carrier rawWitness)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have witnessStrengthens :
      (rawWitness.rename forwardRename).partialStrengthen? renameInverse
        = some rawWitness := by
    rw [RawTerm.partialStrengthen?_rename_some rawWitness forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rawWitness]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noWitnessSuccess =>
      exact absurd (witnessStrengthens.symm.trans noWitnessSuccess)
        (by intro contra; cases contra)
    next targetWitness witnessSuccess =>
      have witnessEq : targetWitness = rawWitness :=
        Option.some.inj (witnessSuccess.symm.trans witnessStrengthens)
      subst witnessEq
      rfl

/-- Parametric-atomic strength-T1 case: `Term.idStrictRefl`.

Strict-identity refl with mode-equality witness, carrier Ty, and
rawWitness RawTerm.  Same two-payload subst pattern as `refl`. -/
theorem strengthenTyped?_rename_eq_idStrictRefl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
            rawWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
            rawWitness)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have witnessStrengthens :
      (rawWitness.rename forwardRename).partialStrengthen? renameInverse
        = some rawWitness := by
    rw [RawTerm.partialStrengthen?_rename_some rawWitness forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rawWitness]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noWitnessSuccess =>
      exact absurd (witnessStrengthens.symm.trans noWitnessSuccess)
        (by intro contra; cases contra)
    next targetWitness witnessSuccess =>
      have witnessEq : targetWitness = rawWitness :=
        Option.some.inj (witnessSuccess.symm.trans witnessStrengthens)
      subst witnessEq
      rfl

/-- Parametric-atomic strength-T1 case: `Term.equivReflIdAtId`.

Identity-as-equivalence at universe-id type: carrier Ty + carrierRaw
RawTerm + universe level witnesses. -/
theorem strengthenTyped?_rename_eq_equivReflIdAtId
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrier : Ty level sourceScope} {carrierRaw : RawTerm sourceScope} :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivReflIdAtId (context := sourceCtx) innerLevel innerLevelLt
            carrier carrierRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivReflIdAtId (context := sourceCtx) innerLevel innerLevelLt
            carrier carrierRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have carrierRawStrengthens :
      (carrierRaw.rename forwardRename).partialStrengthen? renameInverse
        = some carrierRaw := by
    rw [RawTerm.partialStrengthen?_rename_some carrierRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity carrierRaw]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noCarrierRawSuccess =>
      exact absurd (carrierRawStrengthens.symm.trans noCarrierRawSuccess)
        (by intro contra; cases contra)
    next targetCarrierRaw carrierRawSuccess =>
      have carrierRawEq : targetCarrierRaw = carrierRaw :=
        Option.some.inj (carrierRawSuccess.symm.trans carrierRawStrengthens)
      subst carrierRawEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.natSucc`.

The dispatcher recurses on the predecessor through `partialStrengthenTyped?`
and combines the inner success with `partialStrengthenTypedNatSucc`.  The
inductive hypothesis supplies the predecessor's renaming-image equation;
the post-IH proof rewrites the inner match and then closes by `rfl`. -/
theorem strengthenTyped?_rename_eq_natSucc
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {predecessorRaw : RawTerm sourceScope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming predecessor)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            predecessor)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.natSucc predecessor))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.natSucc predecessor)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noPredecessorSuccess =>
    exact absurd (predecessorIH.symm.trans noPredecessorSuccess)
      (by intro contra; cases contra)
  next predecessorResult predecessorSuccess =>
    have resultEq : predecessorResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects predecessor :=
      Option.some.inj (predecessorSuccess.symm.trans predecessorIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.intervalOpp`.

Same shape as `natSucc`: dispatcher recurses on the inner interval value
and combines through `partialStrengthenTypedIntervalOpp`.  The Ty payload
is the closed type `Ty.interval`, so no Ty-witness is needed. -/
theorem strengthenTyped?_rename_eq_intervalOpp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalOpp innerValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.intervalOpp innerValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerValue :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.modIntro`.

Modal introduction wraps a single inner Term IH; no Ty payload (innerType
is inferred from the inner term's typing).  The dispatcher arm recurses
on the inner term and combines through `partialStrengthenTypedModIntro`. -/
theorem strengthenTyped?_rename_eq_modIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modIntro innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.modIntro innerTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerTerm :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.modElim`. -/
theorem strengthenTyped?_rename_eq_modElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modElim innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.modElim innerTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerTerm :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.subsume`. -/
theorem strengthenTyped?_rename_eq_subsume
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.subsume innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.subsume innerTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noInnerSuccess =>
    exact absurd (innerIH.symm.trans noInnerSuccess)
      (by intro contra; cases contra)
  next innerResult innerSuccess =>
    have resultEq : innerResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects innerTerm :=
      Option.some.inj (innerSuccess.symm.trans innerIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.optionSome`.

Wraps a single Term IH; the elementType is implicit (carried through the
inner term's typing).  Dispatcher recurses on the value and combines
through `partialStrengthenTypedOptionSome`. -/
theorem strengthenTyped?_rename_eq_optionSome
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.optionSome valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.optionSome valueTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noValueSuccess =>
    exact absurd (valueIH.symm.trans noValueSuccess)
      (by intro contra; cases contra)
  next valueResult valueSuccess =>
    have resultEq : valueResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects valueTerm :=
      Option.some.inj (valueSuccess.symm.trans valueIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.eitherInl`.

Carries an inner Term IH plus an unused right-type Ty payload.  The
dispatcher first matches the right-type's renaming-image (via
subst-via-witness) then recurses on the value Term. -/
theorem strengthenTyped?_rename_eq_eitherInl
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInl (rightType := rightType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherInl (rightType := rightType) valueTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have rightTypeStrengthens :
      (rightType.rename forwardRename).partialStrengthen? renameInverse
        = some rightType := by
    rw [Ty.partialStrengthen?_rename_some rightType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity rightType]
  split
  next noRightSuccess =>
    exact absurd (rightTypeStrengthens.symm.trans noRightSuccess)
      (by intro contra; cases contra)
  next targetRightType rightSuccess =>
    have rightEq : targetRightType = rightType :=
      Option.some.inj (rightSuccess.symm.trans rightTypeStrengthens)
    subst rightEq
    split
    next noValueSuccess =>
      exact absurd (valueIH.symm.trans noValueSuccess)
        (by intro contra; cases contra)
    next valueResult valueSuccess =>
      have resultEq : valueResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects valueTerm :=
        Option.some.inj (valueSuccess.symm.trans valueIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.eitherInr`.

Mirror of `eitherInl`: unused left-type Ty payload plus inner Term IH. -/
theorem strengthenTyped?_rename_eq_eitherInr
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInr (leftType := leftType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherInr (leftType := leftType) valueTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftTypeStrengthens :
      (leftType.rename forwardRename).partialStrengthen? renameInverse
        = some leftType := by
    rw [Ty.partialStrengthen?_rename_some leftType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity leftType]
  split
  next noLeftSuccess =>
    exact absurd (leftTypeStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftType leftSuccess =>
    have leftEq : targetLeftType = leftType :=
      Option.some.inj (leftSuccess.symm.trans leftTypeStrengthens)
    subst leftEq
    split
    next noValueSuccess =>
      exact absurd (valueIH.symm.trans noValueSuccess)
        (by intro contra; cases contra)
    next valueResult valueSuccess =>
      have resultEq : valueResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects valueTerm :=
        Option.some.inj (valueSuccess.symm.trans valueIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.sessionRecv`.

Carries an inner channel Term IH plus an unused protocolStep RawTerm
payload.  The dispatcher first matches the protocolStep's renaming-image
(via subst-via-witness at the raw layer) then recurses on the channel. -/
theorem strengthenTyped?_rename_eq_sessionRecv
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (channelIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            channel)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.sessionRecv channel))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sessionRecv channel)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have protocolStrengthens :
      (protocolStep.rename forwardRename).partialStrengthen? renameInverse
        = some protocolStep := by
    rw [RawTerm.partialStrengthen?_rename_some protocolStep forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity protocolStep]
  split
  next noProtocolSuccess =>
    exact absurd (protocolStrengthens.symm.trans noProtocolSuccess)
      (by intro contra; cases contra)
  next targetProtocolStep protocolSuccess =>
    have protocolEq : targetProtocolStep = protocolStep :=
      Option.some.inj (protocolSuccess.symm.trans protocolStrengthens)
    subst protocolEq
    split
    next noChannelSuccess =>
      exact absurd (channelIH.symm.trans noChannelSuccess)
        (by intro contra; cases contra)
    next channelResult channelSuccess =>
      have resultEq : channelResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects channel :=
        Option.some.inj (channelSuccess.symm.trans channelIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.cumulUp`.

Cumulativity promotion wraps a single Term IH plus value-level universe
data (lower/higher levels, monotonicity proof, level-fits-in-universe
witnesses); none of those are scope-indexed, so no Ty/Raw witness is
needed.  Dispatcher recurses on the type-code and combines through
`partialStrengthenTypedCumulUp`. -/
theorem strengthenTyped?_rename_eq_cumulUp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (codeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming typeCode)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            typeCode)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
            levelLeHigh typeCode))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
            levelLeHigh typeCode)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noCodeSuccess =>
    exact absurd (codeIH.symm.trans noCodeSuccess)
      (by intro contra; cases contra)
  next codeResult codeSuccess =>
    have resultEq : codeResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects typeCode :=
      Option.some.inj (codeSuccess.symm.trans codeIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.recordProj`.

Single-field record projection wraps a record Term IH and a Ty payload
(`singleFieldType`).  Dispatcher matches the singleFieldType's renaming-
image first (via subst-via-witness), then recurses on the record value. -/
theorem strengthenTyped?_rename_eq_recordProj
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (recordIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming recordValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            recordValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordProj recordValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.recordProj recordValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have fieldStrengthens :
      (singleFieldType.rename forwardRename).partialStrengthen? renameInverse
        = some singleFieldType := by
    rw [Ty.partialStrengthen?_rename_some singleFieldType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity singleFieldType]
  split
  next noFieldSuccess =>
    exact absurd (fieldStrengthens.symm.trans noFieldSuccess)
      (by intro contra; cases contra)
  next targetFieldType fieldSuccess =>
    have fieldEq : targetFieldType = singleFieldType :=
      Option.some.inj (fieldSuccess.symm.trans fieldStrengthens)
    subst fieldEq
    split
    next noRecordSuccess =>
      exact absurd (recordIH.symm.trans noRecordSuccess)
        (by intro contra; cases contra)
    next recordResult recordSuccess =>
      have resultEq : recordResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects recordValue :=
        Option.some.inj (recordSuccess.symm.trans recordIH)
      subst resultEq
      rfl

/-- 1-IH non-binder strength-T1 case: `Term.codataDest`.

Codata destruction wraps a single codata Term IH and two Ty payloads
(`stateType`, `outputType`).  Dispatcher matches the two Ty's renaming-
images first (via two sequential subst-via-witness steps), then recurses
on the codata value. -/
theorem strengthenTyped?_rename_eq_codataDest
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    (codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    (codataIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming codataValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            codataValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.codataDest codataValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.codataDest codataValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have stateStrengthens :
      (stateType.rename forwardRename).partialStrengthen? renameInverse
        = some stateType := by
    rw [Ty.partialStrengthen?_rename_some stateType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity stateType]
  have outputStrengthens :
      (outputType.rename forwardRename).partialStrengthen? renameInverse
        = some outputType := by
    rw [Ty.partialStrengthen?_rename_some outputType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity outputType]
  split
  next noStateSuccess =>
    exact absurd (stateStrengthens.symm.trans noStateSuccess)
      (by intro contra; cases contra)
  next targetStateType stateSuccess =>
    have stateEq : targetStateType = stateType :=
      Option.some.inj (stateSuccess.symm.trans stateStrengthens)
    subst stateEq
    split
    next noOutputSuccess =>
      exact absurd (outputStrengthens.symm.trans noOutputSuccess)
        (by intro contra; cases contra)
    next targetOutputType outputSuccess =>
      have outputEq : targetOutputType = outputType :=
        Option.some.inj (outputSuccess.symm.trans outputStrengthens)
      subst outputEq
      split
      next noCodataSuccess =>
        exact absurd (codataIH.symm.trans noCodataSuccess)
          (by intro contra; cases contra)
      next codataResult codataSuccess =>
        have resultEq : codataResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              codataValue :=
          Option.some.inj (codataSuccess.symm.trans codataIH)
        subst resultEq
        rfl

/-- 1-IH non-binder strength-T1 case: `Term.recordIntro`.

Single-field record introduction wraps a single Term IH for the field
value; `singleFieldType` is implicit (carried through the field's
typing).  Same shape as `optionSome` — dispatcher recurses on the field
and combines through `partialStrengthenTypedRecordIntro`. -/
theorem strengthenTyped?_rename_eq_recordIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    (fieldIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming firstField)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            firstField)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordIntro firstField))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.recordIntro firstField)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noFieldSuccess =>
    exact absurd (fieldIH.symm.trans noFieldSuccess)
      (by intro contra; cases contra)
  next fieldResult fieldSuccess =>
    have resultEq : fieldResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects firstField :=
      Option.some.inj (fieldSuccess.symm.trans fieldIH)
    subst resultEq
    rfl

/-- 1-IH non-binder strength-T1 case: `Term.glueElim`.

Cubical glue elimination wraps a single glued-value Term IH plus a Ty
payload (`baseType`), a RawTerm payload (`boundaryWitness`), and a mode-
univalence equality.  Dispatcher first matches baseType, then
boundaryWitness, then recurses on the glued value. -/
theorem strengthenTyped?_rename_eq_glueElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming gluedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            gluedValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.glueElim modeIsUnivalent gluedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.glueElim modeIsUnivalent gluedValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have baseStrengthens :
      (baseType.rename forwardRename).partialStrengthen? renameInverse
        = some baseType := by
    rw [Ty.partialStrengthen?_rename_some baseType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity baseType]
  have boundaryStrengthens :
      (boundaryWitness.rename forwardRename).partialStrengthen? renameInverse
        = some boundaryWitness := by
    rw [RawTerm.partialStrengthen?_rename_some boundaryWitness forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity boundaryWitness]
  split
  next noBaseSuccess =>
    exact absurd (baseStrengthens.symm.trans noBaseSuccess)
      (by intro contra; cases contra)
  next targetBaseType baseSuccess =>
    have baseEq : targetBaseType = baseType :=
      Option.some.inj (baseSuccess.symm.trans baseStrengthens)
    subst baseEq
    split
    next noBoundarySuccess =>
      exact absurd (boundaryStrengthens.symm.trans noBoundarySuccess)
        (by intro contra; cases contra)
    next targetBoundary boundarySuccess =>
      have boundaryEq : targetBoundary = boundaryWitness :=
        Option.some.inj (boundarySuccess.symm.trans boundaryStrengthens)
      subst boundaryEq
      split
      next noGluedSuccess =>
        exact absurd (gluedIH.symm.trans noGluedSuccess)
          (by intro contra; cases contra)
      next gluedResult gluedSuccess =>
        have resultEq : gluedResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              gluedValue :=
          Option.some.inj (gluedSuccess.symm.trans gluedIH)
        subst resultEq
        rfl

/-- 2-IH non-binder strength-T1 case: `Term.listCons`.

Combines a head Term IH (at `elementType`) with a tail Term IH (at
`Ty.listType elementType`).  No Ty witnesses needed: the dispatcher
recurses directly via `partialStrengthenTypedListCons`. -/
theorem strengthenTyped?_rename_eq_listCons
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headTerm : Term sourceCtx elementType headRaw)
    (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming headTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            headTerm))
    (tailIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming tailTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            tailTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.listCons headTerm tailTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.listCons headTerm tailTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noHeadSuccess =>
    exact absurd (headIH.symm.trans noHeadSuccess)
      (by intro contra; cases contra)
  next headResult headSuccess =>
    have headEq : headResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects headTerm :=
      Option.some.inj (headSuccess.symm.trans headIH)
    subst headEq
    split
    next noTailSuccess =>
      exact absurd (tailIH.symm.trans noTailSuccess)
        (by intro contra; cases contra)
    next tailResult tailSuccess =>
      have tailEq : tailResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects tailTerm :=
        Option.some.inj (tailSuccess.symm.trans tailIH)
      subst tailEq
      rfl

/-- 3-IH non-binder strength-T1 case: `Term.natElim`.

Carries three Term IHs (scrutinee at `Ty.nat`, zero-branch at motive,
succ-branch at `Ty.arrow Ty.nat motive`).  The motiveType is closed —
the dispatcher does not strengthen it directly here; the term's typing
carries it.  No Ty witnesses required. -/
theorem strengthenTyped?_rename_eq_natElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (zeroIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            zeroBranch))
    (succIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            succBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natElim scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.natElim scrutinee zeroBranch succBranch)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noScrutSuccess =>
    exact absurd (scrutineeIH.symm.trans noScrutSuccess)
      (by intro contra; cases contra)
  next scrutResult scrutSuccess =>
    have scrutEq : scrutResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects scrutinee :=
      Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
    subst scrutEq
    split
    next noZeroSuccess =>
      exact absurd (zeroIH.symm.trans noZeroSuccess)
        (by intro contra; cases contra)
    next zeroResult zeroSuccess =>
      have zeroEq : zeroResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects zeroBranch :=
        Option.some.inj (zeroSuccess.symm.trans zeroIH)
      subst zeroEq
      split
      next noSuccSuccess =>
        exact absurd (succIH.symm.trans noSuccSuccess)
          (by intro contra; cases contra)
      next succResult succSuccess =>
        have succEq : succResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects succBranch :=
          Option.some.inj (succSuccess.symm.trans succIH)
        subst succEq
        rfl

/-- 3-IH non-binder strength-T1 case: `Term.natRec`.

Mirror of `natElim` with the binary-succ branch (recursive carrier).
Same dispatcher shape — three Term IHs, no Ty witnesses. -/
theorem strengthenTyped?_rename_eq_natRec
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (zeroIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            zeroBranch))
    (succIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            succBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natRec scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.natRec scrutinee zeroBranch succBranch)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noScrutSuccess =>
    exact absurd (scrutineeIH.symm.trans noScrutSuccess)
      (by intro contra; cases contra)
  next scrutResult scrutSuccess =>
    have scrutEq : scrutResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects scrutinee :=
      Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
    subst scrutEq
    split
    next noZeroSuccess =>
      exact absurd (zeroIH.symm.trans noZeroSuccess)
        (by intro contra; cases contra)
    next zeroResult zeroSuccess =>
      have zeroEq : zeroResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects zeroBranch :=
        Option.some.inj (zeroSuccess.symm.trans zeroIH)
      subst zeroEq
      split
      next noSuccSuccess =>
        exact absurd (succIH.symm.trans noSuccSuccess)
          (by intro contra; cases contra)
      next succResult succSuccess =>
        have succEq : succResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects succBranch :=
          Option.some.inj (succSuccess.symm.trans succIH)
        subst succEq
        rfl

/-- 2-IH non-binder strength-T1 case: `Term.app`.

Non-dep function application: domainType and codomainType are both
unbinder.  Combines two Ty witnesses (domain, codomain) with two Term
IHs (function, argument).  Dispatcher delegates through
`partialStrengthenTypedApp` and its `AppOfSuccess` two-stage helper —
the `subst` pattern propagates equalities through both layers. -/
theorem strengthenTyped?_rename_eq_app
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming functionTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            functionTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.app functionTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.app functionTerm argumentTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainType.rename forwardRename).partialStrengthen? renameInverse
        = some domainType := by
    rw [Ty.partialStrengthen?_rename_some domainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity domainType]
  have codomainStrengthens :
      (codomainType.rename forwardRename).partialStrengthen? renameInverse
        = some codomainType := by
    rw [Ty.partialStrengthen?_rename_some codomainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity codomainType]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainType domainSuccess =>
    have domainEq : targetDomainType = domainType :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainType codomainSuccess =>
      have codomainEq : targetCodomainType = codomainType :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      split
      next noFunctionSuccess =>
        exact absurd (functionIH.symm.trans noFunctionSuccess)
          (by intro contra; cases contra)
      next functionResult functionSuccess =>
        have functionEq : functionResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              functionTerm :=
          Option.some.inj (functionSuccess.symm.trans functionIH)
        subst functionEq
        split
        next noArgumentSuccess =>
          exact absurd (argumentIH.symm.trans noArgumentSuccess)
            (by intro contra; cases contra)
        next argumentResult argumentSuccess =>
          have argumentEq : argumentResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                argumentTerm :=
            Option.some.inj (argumentSuccess.symm.trans argumentIH)
          subst argumentEq
          rfl

/-- 3-IH non-binder strength-T1 case: `Term.listElim`.

Combines an elementType Ty witness (unbinder) with three Term IHs
(scrutinee at `Ty.listType`, nil-branch at motive, cons-branch at
the nested arrow).  The dispatcher delegates through
`partialStrengthenTypedListElim` which uses a `ListElimOfSuccess`
two-stage helper — `subst` rewrites through both layers cleanly. -/
theorem strengthenTyped?_rename_eq_listElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term sourceCtx motiveType nilRaw)
    (consBranch :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (nilIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming nilBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            nilBranch))
    (consIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming consBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            consBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listElim scrutinee nilBranch consBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.listElim scrutinee nilBranch consBranch)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse
        = some elementType := by
    rw [Ty.partialStrengthen?_rename_some elementType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity elementType]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementType elementSuccess =>
    have elementEq : targetElementType = elementType :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    split
    next noScrutSuccess =>
      exact absurd (scrutineeIH.symm.trans noScrutSuccess)
        (by intro contra; cases contra)
    next scrutResult scrutSuccess =>
      have scrutEq : scrutResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects scrutinee :=
        Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
      subst scrutEq
      split
      next noNilSuccess =>
        exact absurd (nilIH.symm.trans noNilSuccess)
          (by intro contra; cases contra)
      next nilResult nilSuccess =>
        have nilEq : nilResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects nilBranch :=
          Option.some.inj (nilSuccess.symm.trans nilIH)
        subst nilEq
        split
        next noConsSuccess =>
          exact absurd (consIH.symm.trans noConsSuccess)
            (by intro contra; cases contra)
        next consResult consSuccess =>
          have consEq : consResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                consBranch :=
            Option.some.inj (consSuccess.symm.trans consIH)
          subst consEq
          rfl

/-- 3-IH non-binder strength-T1 case: `Term.optionMatch`.

Combines an elementType Ty witness with three Term IHs (scrutinee at
`Ty.optionType`, none-branch at motive, some-branch at the arrow
`elementType -> motive`).  Same shape as `listElim`. -/
theorem strengthenTyped?_rename_eq_optionMatch
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term sourceCtx motiveType noneRaw)
    (someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (noneIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming noneBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            noneBranch))
    (someIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming someBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            someBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionMatch scrutinee noneBranch someBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.optionMatch scrutinee noneBranch someBranch)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementType.rename forwardRename).partialStrengthen? renameInverse
        = some elementType := by
    rw [Ty.partialStrengthen?_rename_some elementType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity elementType]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementType elementSuccess =>
    have elementEq : targetElementType = elementType :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    split
    next noScrutSuccess =>
      exact absurd (scrutineeIH.symm.trans noScrutSuccess)
        (by intro contra; cases contra)
    next scrutResult scrutSuccess =>
      have scrutEq : scrutResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects scrutinee :=
        Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
      subst scrutEq
      split
      next noNoneSuccess =>
        exact absurd (noneIH.symm.trans noNoneSuccess)
          (by intro contra; cases contra)
      next noneResult noneSuccess =>
        have noneEq : noneResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              noneBranch :=
          Option.some.inj (noneSuccess.symm.trans noneIH)
        subst noneEq
        split
        next noSomeSuccess =>
          exact absurd (someIH.symm.trans noSomeSuccess)
            (by intro contra; cases contra)
        next someResult someSuccess =>
          have someEq : someResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                someBranch :=
            Option.some.inj (someSuccess.symm.trans someIH)
          subst someEq
          rfl

/-- 3-IH non-binder strength-T1 case: `Term.eitherMatch`.

Combines THREE Ty witnesses (leftType, rightType, motiveType — all
unbinder) with three Term IHs (scrutinee, leftBranch, rightBranch).
Six sequential subst-via-witness blocks; the longest atomic ctor in
the strength-T1 cascade. -/
theorem strengthenTyped?_rename_eq_eitherMatch
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    (scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftBranch))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightBranch)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherMatch scrutinee leftBranch rightBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherMatch scrutinee leftBranch rightBranch)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftTypeStrengthens :
      (leftType.rename forwardRename).partialStrengthen? renameInverse
        = some leftType := by
    rw [Ty.partialStrengthen?_rename_some leftType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity leftType]
  have rightTypeStrengthens :
      (rightType.rename forwardRename).partialStrengthen? renameInverse
        = some rightType := by
    rw [Ty.partialStrengthen?_rename_some rightType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity rightType]
  have motiveTypeStrengthens :
      (motiveType.rename forwardRename).partialStrengthen? renameInverse
        = some motiveType := by
    rw [Ty.partialStrengthen?_rename_some motiveType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity motiveType]
  split
  next noLeftSuccess =>
    exact absurd (leftTypeStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftType leftSuccess =>
    have leftEq : targetLeftType = leftType :=
      Option.some.inj (leftSuccess.symm.trans leftTypeStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightTypeStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightType rightSuccess =>
      have rightEq : targetRightType = rightType :=
        Option.some.inj (rightSuccess.symm.trans rightTypeStrengthens)
      subst rightEq
      split
      next noMotiveSuccess =>
        exact absurd (motiveTypeStrengthens.symm.trans noMotiveSuccess)
          (by intro contra; cases contra)
      next targetMotiveType motiveSuccess =>
        have motiveEq : targetMotiveType = motiveType :=
          Option.some.inj (motiveSuccess.symm.trans motiveTypeStrengthens)
        subst motiveEq
        split
        next noScrutSuccess =>
          exact absurd (scrutineeIH.symm.trans noScrutSuccess)
            (by intro contra; cases contra)
        next scrutResult scrutSuccess =>
          have scrutEq : scrutResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                scrutinee :=
            Option.some.inj (scrutSuccess.symm.trans scrutineeIH)
          subst scrutEq
          split
          next noLeftBranchSuccess =>
            exact absurd (leftIH.symm.trans noLeftBranchSuccess)
              (by intro contra; cases contra)
          next leftResult leftBranchSuccess =>
            have leftBranchEq : leftResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  leftBranch :=
              Option.some.inj (leftBranchSuccess.symm.trans leftIH)
            subst leftBranchEq
            split
            next noRightBranchSuccess =>
              exact absurd (rightIH.symm.trans noRightBranchSuccess)
                (by intro contra; cases contra)
            next rightResult rightBranchSuccess =>
              have rightBranchEq : rightResult =
                  StrengtheningResult.fromRename forwardRename typedRenaming
                    renameInverse renameInverseLeft renameInverseInjects
                    rightBranch :=
                Option.some.inj (rightBranchSuccess.symm.trans rightIH)
              subst rightBranchEq
              rfl

/-- 2-IH non-binder strength-T1 case: `Term.idJ`.

HoTT identity-type eliminator: combines one Ty witness (carrier), two
RawTerm witnesses (leftEndpoint, rightEndpoint), and two Term IHs
(baseCase, witness).  All payloads are unbinder. -/
theorem strengthenTyped?_rename_eq_idJ
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseCase))
    (witnessIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            witness)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.idJ baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.idJ baseCase witness)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noBaseSuccess =>
          exact absurd (baseIH.symm.trans noBaseSuccess)
            (by intro contra; cases contra)
        next baseResult baseSuccess =>
          have baseEq : baseResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                baseCase :=
            Option.some.inj (baseSuccess.symm.trans baseIH)
          subst baseEq
          split
          next noWitnessSuccess =>
            exact absurd (witnessIH.symm.trans noWitnessSuccess)
              (by intro contra; cases contra)
          next witnessResult witnessSuccess =>
            have witnessEq : witnessResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  witness :=
              Option.some.inj (witnessSuccess.symm.trans witnessIH)
            subst witnessEq
            rfl

/-- 2-IH non-binder strength-T1 case: `Term.oeqJ`.

Observational-equality eliminator: mirror of `idJ` with `Ty.oeq` in
place of `Ty.id`.  Same shape — one Ty witness, two RawTerm witnesses,
two Term IHs. -/
theorem strengthenTyped?_rename_eq_oeqJ
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseCase))
    (witnessIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            witness)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.oeqJ baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.oeqJ baseCase witness)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noBaseSuccess =>
          exact absurd (baseIH.symm.trans noBaseSuccess)
            (by intro contra; cases contra)
        next baseResult baseSuccess =>
          have baseEq : baseResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                baseCase :=
            Option.some.inj (baseSuccess.symm.trans baseIH)
          subst baseEq
          split
          next noWitnessSuccess =>
            exact absurd (witnessIH.symm.trans noWitnessSuccess)
              (by intro contra; cases contra)
          next witnessResult witnessSuccess =>
            have witnessEq : witnessResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  witness :=
              Option.some.inj (witnessSuccess.symm.trans witnessIH)
            subst witnessEq
            rfl

/-- 2-IH non-binder strength-T1 case: `Term.idStrictRec`.

Strict-identity eliminator: mirror of `idJ` with `Ty.idStrict` and an
extra `modeIsStrict` carrier proof.  Same dispatcher shape — one Ty
witness, two RawTerm witnesses, two Term IHs. -/
theorem strengthenTyped?_rename_eq_idStrictRec
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseCase))
    (witnessIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            witness)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idStrictRec modeIsStrict baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.idStrictRec modeIsStrict baseCase witness)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse
        = some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noBaseSuccess =>
          exact absurd (baseIH.symm.trans noBaseSuccess)
            (by intro contra; cases contra)
        next baseResult baseSuccess =>
          have baseEq : baseResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                baseCase :=
            Option.some.inj (baseSuccess.symm.trans baseIH)
          subst baseEq
          split
          next noWitnessSuccess =>
            exact absurd (witnessIH.symm.trans noWitnessSuccess)
              (by intro contra; cases contra)
          next witnessResult witnessSuccess =>
            have witnessEq : witnessResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  witness :=
              Option.some.inj (witnessSuccess.symm.trans witnessIH)
            subst witnessEq
            rfl

/-- 2-IH non-binder strength-T1 case: `Term.intervalMeet`.

Combines two Term IHs (leftValue, rightValue at `Ty.interval`).
No Ty witnesses — both arguments live at the closed type
`Ty.interval`.  Dispatcher recurses directly via
`partialStrengthenTypedIntervalMeet`. -/
theorem strengthenTyped?_rename_eq_intervalMeet
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftValue))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalMeet leftValue rightValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.intervalMeet leftValue rightValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noLeftSuccess =>
    exact absurd (leftIH.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next leftResult leftSuccess =>
    have leftEq : leftResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects leftValue :=
      Option.some.inj (leftSuccess.symm.trans leftIH)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightIH.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next rightResult rightSuccess =>
      have rightEq : rightResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects rightValue :=
        Option.some.inj (rightSuccess.symm.trans rightIH)
      subst rightEq
      rfl

/-- 2-IH non-binder strength-T1 case: `Term.intervalJoin`.

Mirror of `intervalMeet`: two interval-typed Term IHs combined via
`partialStrengthenTypedIntervalJoin`. -/
theorem strengthenTyped?_rename_eq_intervalJoin
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftValue))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalJoin leftValue rightValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.intervalJoin leftValue rightValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noLeftSuccess =>
    exact absurd (leftIH.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next leftResult leftSuccess =>
    have leftEq : leftResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects leftValue :=
      Option.some.inj (leftSuccess.symm.trans leftIH)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightIH.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next rightResult rightSuccess =>
      have rightEq : rightResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects rightValue :=
        Option.some.inj (rightSuccess.symm.trans rightIH)
      subst rightEq
      rfl

/-- 2-IH non-binder strength-T1 case: `Term.hcomp`.

Homogeneous composition (univalent-only).  Combines two Term IHs
(sidesValue, capValue at `carrierType`).  The carrierType is NOT
strengthened by the dispatcher — it's carried opaquely through the
result.  Mode is constrained via `modeIsUnivalent`. -/
theorem strengthenTyped?_rename_eq_hcomp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    (sidesValue : Term sourceCtx carrierType sidesRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming sidesValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            sidesValue))
    (capIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming capValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            capValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.hcomp modeIsUnivalent sidesValue capValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.hcomp modeIsUnivalent sidesValue capValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  split
  next noSidesSuccess =>
    exact absurd (sidesIH.symm.trans noSidesSuccess)
      (by intro contra; cases contra)
  next sidesResult sidesSuccess =>
    have sidesEq : sidesResult =
        StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects sidesValue :=
      Option.some.inj (sidesSuccess.symm.trans sidesIH)
    subst sidesEq
    split
    next noCapSuccess =>
      exact absurd (capIH.symm.trans noCapSuccess)
        (by intro contra; cases contra)
    next capResult capSuccess =>
      have capEq : capResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects capValue :=
        Option.some.inj (capSuccess.symm.trans capIH)
      subst capEq
      rfl

/-- Type-code strength-T1 case: `Term.listCode`.

Single RawTerm payload (`elementCodeRaw`).  Dispatcher matches the
renamed RawTerm's strengthening via subst-via-witness on
`RawTerm.partialStrengthen?_rename_some`. -/
theorem strengthenTyped?_rename_eq_listCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.listCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some elementCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some elementCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity elementCodeRaw]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementCodeRaw elementSuccess =>
    have elementEq : targetElementCodeRaw = elementCodeRaw :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    rfl

/-- Type-code strength-T1 case: `Term.optionCode`. -/
theorem strengthenTyped?_rename_eq_optionCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.optionCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have elementStrengthens :
      (elementCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some elementCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some elementCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity elementCodeRaw]
  split
  next noElementSuccess =>
    exact absurd (elementStrengthens.symm.trans noElementSuccess)
      (by intro contra; cases contra)
  next targetElementCodeRaw elementSuccess =>
    have elementEq : targetElementCodeRaw = elementCodeRaw :=
      Option.some.inj (elementSuccess.symm.trans elementStrengthens)
    subst elementEq
    rfl

/-- Type-code strength-T1 case: `Term.arrowCode`.

Non-binder shape: both `domainCodeRaw` and `codomainCodeRaw` rename
via `rho` at the outer scope. -/
theorem strengthenTyped?_rename_eq_arrowCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.arrowCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.arrowCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some domainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some domainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity domainCodeRaw]
  have codomainStrengthens :
      (codomainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some codomainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some codomainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity codomainCodeRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainCodeRaw domainSuccess =>
    have domainEq : targetDomainCodeRaw = domainCodeRaw :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainCodeRaw codomainSuccess =>
      have codomainEq : targetCodomainCodeRaw = codomainCodeRaw :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      rfl

/-- Type-code strength-T1 case: `Term.sumCode`. -/
theorem strengthenTyped?_rename_eq_sumCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sumCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sumCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftStrengthens :
      (leftCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftCodeRaw]
  have rightStrengthens :
      (rightCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightCodeRaw]
  split
  next noLeftSuccess =>
    exact absurd (leftStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftCodeRaw leftSuccess =>
    have leftEq : targetLeftCodeRaw = leftCodeRaw :=
      Option.some.inj (leftSuccess.symm.trans leftStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightCodeRaw rightSuccess =>
      have rightEq : targetRightCodeRaw = rightCodeRaw :=
        Option.some.inj (rightSuccess.symm.trans rightStrengthens)
      subst rightEq
      rfl

/-- Type-code strength-T1 case: `Term.productCode`. -/
theorem strengthenTyped?_rename_eq_productCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.productCode (context := sourceCtx) outerLevel levelLe
            firstCodeRaw secondCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.productCode (context := sourceCtx) outerLevel levelLe
            firstCodeRaw secondCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have firstStrengthens :
      (firstCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some firstCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some firstCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity firstCodeRaw]
  have secondStrengthens :
      (secondCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some secondCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some secondCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity secondCodeRaw]
  split
  next noFirstSuccess =>
    exact absurd (firstStrengthens.symm.trans noFirstSuccess)
      (by intro contra; cases contra)
  next targetFirstCodeRaw firstSuccess =>
    have firstEq : targetFirstCodeRaw = firstCodeRaw :=
      Option.some.inj (firstSuccess.symm.trans firstStrengthens)
    subst firstEq
    split
    next noSecondSuccess =>
      exact absurd (secondStrengthens.symm.trans noSecondSuccess)
        (by intro contra; cases contra)
    next targetSecondCodeRaw secondSuccess =>
      have secondEq : targetSecondCodeRaw = secondCodeRaw :=
        Option.some.inj (secondSuccess.symm.trans secondStrengthens)
      subst secondEq
      rfl

/-- Type-code strength-T1 case: `Term.eitherCode`. -/
theorem strengthenTyped?_rename_eq_eitherCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.eitherCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftStrengthens :
      (leftCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftCodeRaw]
  have rightStrengthens :
      (rightCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightCodeRaw]
  split
  next noLeftSuccess =>
    exact absurd (leftStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftCodeRaw leftSuccess =>
    have leftEq : targetLeftCodeRaw = leftCodeRaw :=
      Option.some.inj (leftSuccess.symm.trans leftStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightCodeRaw rightSuccess =>
      have rightEq : targetRightCodeRaw = rightCodeRaw :=
        Option.some.inj (rightSuccess.symm.trans rightStrengthens)
      subst rightEq
      rfl

/-- Type-code strength-T1 case: `Term.idCode`.

Three RawTerm payloads sequenced. -/
theorem strengthenTyped?_rename_eq_idCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idCode (context := sourceCtx) outerLevel levelLe
            typeCodeRaw leftRaw rightRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.idCode (context := sourceCtx) outerLevel levelLe
            typeCodeRaw leftRaw rightRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have typeStrengthens :
      (typeCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some typeCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some typeCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity typeCodeRaw]
  have leftStrengthens :
      (leftRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftRaw]
  have rightStrengthens :
      (rightRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightRaw]
  split
  next noTypeSuccess =>
    exact absurd (typeStrengthens.symm.trans noTypeSuccess)
      (by intro contra; cases contra)
  next targetTypeCodeRaw typeSuccess =>
    have typeEq : targetTypeCodeRaw = typeCodeRaw :=
      Option.some.inj (typeSuccess.symm.trans typeStrengthens)
    subst typeEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftRaw leftSuccess =>
      have leftEq : targetLeftRaw = leftRaw :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightRaw rightSuccess =>
        have rightEq : targetRightRaw = rightRaw :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        rfl

/-- Type-code strength-T1 case: `Term.equivCode`. -/
theorem strengthenTyped?_rename_eq_equivCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivCode (context := sourceCtx) outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivCode (context := sourceCtx) outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have leftStrengthens :
      (leftTypeCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some leftTypeCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some leftTypeCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftTypeCodeRaw]
  have rightStrengthens :
      (rightTypeCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some rightTypeCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some rightTypeCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightTypeCodeRaw]
  split
  next noLeftSuccess =>
    exact absurd (leftStrengthens.symm.trans noLeftSuccess)
      (by intro contra; cases contra)
  next targetLeftTypeCodeRaw leftSuccess =>
    have leftEq : targetLeftTypeCodeRaw = leftTypeCodeRaw :=
      Option.some.inj (leftSuccess.symm.trans leftStrengthens)
    subst leftEq
    split
    next noRightSuccess =>
      exact absurd (rightStrengthens.symm.trans noRightSuccess)
        (by intro contra; cases contra)
    next targetRightTypeCodeRaw rightSuccess =>
      have rightEq : targetRightTypeCodeRaw = rightTypeCodeRaw :=
        Option.some.inj (rightSuccess.symm.trans rightStrengthens)
      subst rightEq
      rfl

/-- Type-code strength-T1 case: `Term.piTyCode`.

Binder-shape: `domainCodeRaw` renames via `rho` at the outer scope,
`codomainCodeRaw` renames via `rho.lift` under one binder.  The
codomain witness uses
`PartialRawRenaming.lift_rename_some` for survival under the lift,
combined with `RawRenaming.identity_lift_pointwise` + rename_identity
to collapse `codomainCodeRaw.rename id.lift` back to `codomainCodeRaw`. -/
theorem strengthenTyped?_rename_eq_piTyCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.piTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.piTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some domainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some domainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity domainCodeRaw]
  have codomainStrengthens :
      (codomainCodeRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some codomainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some codomainCodeRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) codomainCodeRaw,
      RawTerm.rename_identity codomainCodeRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainCodeRaw domainSuccess =>
    have domainEq : targetDomainCodeRaw = domainCodeRaw :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainCodeRaw codomainSuccess =>
      have codomainEq : targetCodomainCodeRaw = codomainCodeRaw :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      rfl

/-- Type-code strength-T1 case: `Term.sigmaTyCode`.

Binder-shape mirror of `piTyCode`: same survival pattern under the
codomain binder. -/
theorem strengthenTyped?_rename_eq_sigmaTyCode
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainCodeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some domainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some domainCodeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity domainCodeRaw]
  have codomainStrengthens :
      (codomainCodeRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some codomainCodeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some codomainCodeRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) codomainCodeRaw,
      RawTerm.rename_identity codomainCodeRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainCodeRaw domainSuccess =>
    have domainEq : targetDomainCodeRaw = domainCodeRaw :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainCodeRaw codomainSuccess =>
      have codomainEq : targetCodomainCodeRaw = codomainCodeRaw :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      rfl

/-- HoTT-special strength-T1 case: `Term.funextReflAtId`.

Carries 2 Ty payloads at the outer scope (domainType, codomainType)
plus 1 RawTerm payload under one binder (applyRaw via `back.lift`).
The codomain RawTerm `applyRaw` uses the same `rho.lift` survival
recipe as `piTyCode`. -/
theorem strengthenTyped?_rename_eq_funextReflAtId
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {domainType codomainType : Ty level sourceScope}
    (applyRaw : RawTerm (sourceScope + 1)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextReflAtId (context := sourceCtx) domainType codomainType
            applyRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.funextReflAtId (context := sourceCtx) domainType codomainType
            applyRaw)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have domainStrengthens :
      (domainType.rename forwardRename).partialStrengthen? renameInverse
        = some domainType := by
    rw [Ty.partialStrengthen?_rename_some domainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity domainType]
  have codomainStrengthens :
      (codomainType.rename forwardRename).partialStrengthen? renameInverse
        = some codomainType := by
    rw [Ty.partialStrengthen?_rename_some codomainType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity codomainType]
  have applyStrengthens :
      (applyRaw.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some applyRaw := by
    rw [RawTerm.partialStrengthen?_rename_some applyRaw
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) applyRaw,
      RawTerm.rename_identity applyRaw]
  split
  next noDomainSuccess =>
    exact absurd (domainStrengthens.symm.trans noDomainSuccess)
      (by intro contra; cases contra)
  next targetDomainType domainSuccess =>
    have domainEq : targetDomainType = domainType :=
      Option.some.inj (domainSuccess.symm.trans domainStrengthens)
    subst domainEq
    split
    next noCodomainSuccess =>
      exact absurd (codomainStrengthens.symm.trans noCodomainSuccess)
        (by intro contra; cases contra)
    next targetCodomainType codomainSuccess =>
      have codomainEq : targetCodomainType = codomainType :=
        Option.some.inj (codomainSuccess.symm.trans codomainStrengthens)
      subst codomainEq
      split
      next noApplySuccess =>
        exact absurd (applyStrengthens.symm.trans noApplySuccess)
          (by intro contra; cases contra)
      next targetApplyRaw applySuccess =>
        have applyEq : targetApplyRaw = applyRaw :=
          Option.some.inj (applySuccess.symm.trans applyStrengthens)
        subst applyEq
        rfl

/-- HoTT-special strength-T1 case: `Term.refineIntro`.

Carries 1 binder-shape RawTerm payload (`predicate` at `scope+1` via
`back.lift`) plus 2 Term IHs (`baseValue` at `baseType` + `predicateProof`
at `Ty.unit`). -/
theorem strengthenTyped?_rename_eq_refineIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType valueRaw)
    (predicateProof : Term sourceCtx Ty.unit proofRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseValue))
    (proofIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming predicateProof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            predicateProof)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineIntro (context := sourceCtx) predicate baseValue
            predicateProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.refineIntro (context := sourceCtx) predicate baseValue
            predicateProof)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have predicateStrengthens :
      (predicate.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some predicate := by
    rw [RawTerm.partialStrengthen?_rename_some predicate
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) predicate,
      RawTerm.rename_identity predicate]
  split
  next noPredicateSuccess =>
    exact absurd (predicateStrengthens.symm.trans noPredicateSuccess)
      (by intro contra; cases contra)
  next targetPredicate predicateSuccess =>
    have predicateEq : targetPredicate = predicate :=
      Option.some.inj (predicateSuccess.symm.trans predicateStrengthens)
    subst predicateEq
    split
    next noBaseSuccess =>
      exact absurd (baseIH.symm.trans noBaseSuccess)
        (by intro contra; cases contra)
    next baseResult baseSuccess =>
      have baseEq : baseResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects baseValue :=
        Option.some.inj (baseSuccess.symm.trans baseIH)
      subst baseEq
      split
      next noProofSuccess =>
        exact absurd (proofIH.symm.trans noProofSuccess)
          (by intro contra; cases contra)
      next proofResult proofSuccess =>
        have proofEq : proofResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              predicateProof :=
          Option.some.inj (proofSuccess.symm.trans proofIH)
        subst proofEq
        rfl

/-- HoTT-special strength-T1 case: `Term.refineElim`.

Carries 1 Ty payload (`baseType` at outer `back`) + 1 binder-shape
RawTerm payload (`predicate` at `back.lift`) + 1 Term IH
(`refinedValue` at `Ty.refine baseType predicate`).  Both `baseType`
and `predicate` are implicit on the ctor — they reconstruct from the
refinedValue's type. -/
theorem strengthenTyped?_rename_eq_refineElim
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    (refinedValue : Term sourceCtx (Ty.refine baseType predicate) refinedRaw)
    (refinedIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming refinedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            refinedValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineElim (context := sourceCtx) (baseType := baseType)
            (predicate := predicate) refinedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.refineElim (context := sourceCtx) (baseType := baseType)
            (predicate := predicate) refinedValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have baseStrengthens :
      (baseType.rename forwardRename).partialStrengthen? renameInverse
        = some baseType := by
    rw [Ty.partialStrengthen?_rename_some baseType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity baseType]
  have predicateStrengthens :
      (predicate.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift
        = some predicate := by
    rw [RawTerm.partialStrengthen?_rename_some predicate
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) predicate,
      RawTerm.rename_identity predicate]
  split
  next noBaseSuccess =>
    exact absurd (baseStrengthens.symm.trans noBaseSuccess)
      (by intro contra; cases contra)
  next targetBaseType baseSuccess =>
    have baseEq : targetBaseType = baseType :=
      Option.some.inj (baseSuccess.symm.trans baseStrengthens)
    subst baseEq
    split
    next noPredicateSuccess =>
      exact absurd (predicateStrengthens.symm.trans noPredicateSuccess)
        (by intro contra; cases contra)
    next targetPredicate predicateSuccess =>
      have predicateEq : targetPredicate = predicate :=
        Option.some.inj (predicateSuccess.symm.trans predicateStrengthens)
      subst predicateEq
      split
      next noRefinedSuccess =>
        exact absurd (refinedIH.symm.trans noRefinedSuccess)
          (by intro contra; cases contra)
      next refinedResult refinedSuccess =>
        have refinedEq : refinedResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              refinedValue :=
          Option.some.inj (refinedSuccess.symm.trans refinedIH)
        subst refinedEq
        rfl

/-- HoTT-special strength-T1 case: `Term.sessionSend`.

Carries 1 outer-scope RawTerm payload (`protocolStep` at `back`) + 2
Term IHs (`channel` at `Ty.session protocolStep` + `payload` at
`payloadType`).  The `payloadType` itself is implicit — reconstructed
from the payload's type. -/
theorem strengthenTyped?_rename_eq_sessionSend
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (payload : Term sourceCtx payloadType payloadRaw)
    (channelIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            channel))
    (payloadIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming payload)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            payload)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sessionSend (context := sourceCtx) protocolStep channel
            payload))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.sessionSend (context := sourceCtx) protocolStep channel
            payload)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have protocolStrengthens :
      (protocolStep.rename forwardRename).partialStrengthen? renameInverse
        = some protocolStep := by
    rw [RawTerm.partialStrengthen?_rename_some protocolStep forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity protocolStep]
  split
  next noProtocolSuccess =>
    exact absurd (protocolStrengthens.symm.trans noProtocolSuccess)
      (by intro contra; cases contra)
  next targetProtocolStep protocolSuccess =>
    have protocolEq : targetProtocolStep = protocolStep :=
      Option.some.inj (protocolSuccess.symm.trans protocolStrengthens)
    subst protocolEq
    split
    next noChannelSuccess =>
      exact absurd (channelIH.symm.trans noChannelSuccess)
        (by intro contra; cases contra)
    next channelResult channelSuccess =>
      have channelEq : channelResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects channel :=
        Option.some.inj (channelSuccess.symm.trans channelIH)
      subst channelEq
      split
      next noPayloadSuccess =>
        exact absurd (payloadIH.symm.trans noPayloadSuccess)
          (by intro contra; cases contra)
      next payloadResult payloadSuccess =>
        have payloadEq : payloadResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects payload :=
          Option.some.inj (payloadSuccess.symm.trans payloadIH)
        subst payloadEq
        rfl

/-- HoTT-special strength-T1 case: `Term.equivApp`.

Carries 2 Ty payloads (`carrierA + carrierB` at outer `back`) + 2 Term
IHs (`equivTerm` at `Ty.equiv carrierA carrierB` + `argumentTerm` at
`carrierA`).  Both Ty payloads are implicit on the ctor. -/
theorem strengthenTyped?_rename_eq_equivApp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivApp (context := sourceCtx) equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.equivApp (context := sourceCtx) equivTerm argumentTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse
        = some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse
        = some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  split
  next noCarrierASuccess =>
    exact absurd (carrierAStrengthens.symm.trans noCarrierASuccess)
      (by intro contra; cases contra)
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact absurd (carrierBStrengthens.symm.trans noCarrierBSuccess)
        (by intro contra; cases contra)
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noEquivSuccess =>
        exact absurd (equivIH.symm.trans noEquivSuccess)
          (by intro contra; cases contra)
      next equivResult equivSuccess =>
        have equivEq : equivResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              equivTerm :=
          Option.some.inj (equivSuccess.symm.trans equivIH)
        subst equivEq
        split
        next noArgumentSuccess =>
          exact absurd (argumentIH.symm.trans noArgumentSuccess)
            (by intro contra; cases contra)
        next argumentResult argumentSuccess =>
          have argumentEq : argumentResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                argumentTerm :=
            Option.some.inj (argumentSuccess.symm.trans argumentIH)
          subst argumentEq
          rfl

/-- HoTT-special strength-T1 case: `Term.transp`.

Cubical transp carries 2 Ty payloads (sourceType, targetType) + 2
RawTerm payloads (sourceTypeRaw, targetTypeRaw), all at outer
`back`, plus 2 Term IHs (typePath, sourceValue).  No binder lift, no
`▸` cast. -/
theorem strengthenTyped?_rename_eq_transp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term sourceCtx sourceType sourceRaw)
    (pathIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming typePath)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            typePath))
    (sourceIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming sourceValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            sourceValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
            universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
            typePath sourceValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
            universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
            typePath sourceValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have sourceTypeStrengthens :
      (sourceType.rename forwardRename).partialStrengthen? renameInverse
        = some sourceType := by
    rw [Ty.partialStrengthen?_rename_some sourceType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity sourceType]
  have targetTypeStrengthens :
      (targetType.rename forwardRename).partialStrengthen? renameInverse
        = some targetType := by
    rw [Ty.partialStrengthen?_rename_some targetType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity targetType]
  have sourceTypeRawStrengthens :
      (sourceTypeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some sourceTypeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some sourceTypeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity sourceTypeRaw]
  have targetTypeRawStrengthens :
      (targetTypeRaw.rename forwardRename).partialStrengthen? renameInverse
        = some targetTypeRaw := by
    rw [RawTerm.partialStrengthen?_rename_some targetTypeRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity targetTypeRaw]
  split
  next noSourceTypeSuccess =>
    exact absurd (sourceTypeStrengthens.symm.trans noSourceTypeSuccess)
      (by intro contra; cases contra)
  next targetSourceType sourceTypeSuccess =>
    have sourceTypeEq : targetSourceType = sourceType :=
      Option.some.inj (sourceTypeSuccess.symm.trans sourceTypeStrengthens)
    subst sourceTypeEq
    split
    next noTargetTypeSuccess =>
      exact absurd (targetTypeStrengthens.symm.trans noTargetTypeSuccess)
        (by intro contra; cases contra)
    next targetTargetType targetTypeSuccess =>
      have targetTypeEq : targetTargetType = targetType :=
        Option.some.inj (targetTypeSuccess.symm.trans targetTypeStrengthens)
      subst targetTypeEq
      split
      next noSourceTypeRawSuccess =>
        exact absurd
          (sourceTypeRawStrengthens.symm.trans noSourceTypeRawSuccess)
          (by intro contra; cases contra)
      next targetSourceTypeRaw sourceTypeRawSuccess =>
        have sourceTypeRawEq : targetSourceTypeRaw = sourceTypeRaw :=
          Option.some.inj
            (sourceTypeRawSuccess.symm.trans sourceTypeRawStrengthens)
        subst sourceTypeRawEq
        split
        next noTargetTypeRawSuccess =>
          exact absurd
            (targetTypeRawStrengthens.symm.trans noTargetTypeRawSuccess)
            (by intro contra; cases contra)
        next targetTargetTypeRaw targetTypeRawSuccess =>
          have targetTypeRawEq : targetTargetTypeRaw = targetTypeRaw :=
            Option.some.inj
              (targetTypeRawSuccess.symm.trans targetTypeRawStrengthens)
          subst targetTypeRawEq
          split
          next noPathSuccess =>
            exact absurd (pathIH.symm.trans noPathSuccess)
              (by intro contra; cases contra)
          next pathResult pathSuccess =>
            have pathEq : pathResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  typePath :=
              Option.some.inj (pathSuccess.symm.trans pathIH)
            subst pathEq
            split
            next noSourceSuccess =>
              exact absurd (sourceIH.symm.trans noSourceSuccess)
                (by intro contra; cases contra)
            next sourceResult sourceSuccess =>
              have sourceEq : sourceResult =
                  StrengtheningResult.fromRename forwardRename typedRenaming
                    renameInverse renameInverseLeft renameInverseInjects
                    sourceValue :=
                Option.some.inj (sourceSuccess.symm.trans sourceIH)
              subst sourceEq
              rfl

/-- HoTT-special strength-T1 case: `Term.hcompPath`.

Cubical homogeneous path composition: 1 implicit Ty payload
(carrierType at outer `back`) + 2 explicit RawTerm payloads
(leftEndpoint, rightEndpoint at outer `back`) + 2 Term IHs
(sidesPath at `Ty.path carrierType leftEndpoint rightEndpoint` +
capValue at `carrierType`). -/
theorem strengthenTyped?_rename_eq_hcompPath
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    (sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming sidesPath)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            sidesPath))
    (capIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming capValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            capValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.hcompPath (context := sourceCtx) modeIsUnivalent
            leftEndpoint rightEndpoint sidesPath capValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.hcompPath (context := sourceCtx) modeIsUnivalent
            leftEndpoint rightEndpoint sidesPath capValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrierType.rename forwardRename).partialStrengthen? renameInverse
        = some carrierType := by
    rw [Ty.partialStrengthen?_rename_some carrierType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierType]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrierType carrierSuccess =>
    have carrierEq : targetCarrierType = carrierType :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noSidesSuccess =>
          exact absurd (sidesIH.symm.trans noSidesSuccess)
            (by intro contra; cases contra)
        next sidesResult sidesSuccess =>
          have sidesEq : sidesResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                sidesPath :=
            Option.some.inj (sidesSuccess.symm.trans sidesIH)
          subst sidesEq
          split
          next noCapSuccess =>
            exact absurd (capIH.symm.trans noCapSuccess)
              (by intro contra; cases contra)
          next capResult capSuccess =>
            have capEq : capResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  capValue :=
              Option.some.inj (capSuccess.symm.trans capIH)
            subst capEq
            rfl

/-- HoTT-special strength-T1 case: `Term.glueIntro`.

Cubical glue introduction: 1 Ty payload (baseType) + 1 RawTerm
payload (boundaryWitness), both at outer `back`, + 2 Term IHs
(baseValue at `baseType`, partialValue at `baseType`). -/
theorem strengthenTyped?_rename_eq_glueIntro
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType baseRaw)
    (partialValue : Term sourceCtx baseType partialRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseValue))
    (partialIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming partialValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            partialValue)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
            boundaryWitness baseValue partialValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
            boundaryWitness baseValue partialValue)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have baseTypeStrengthens :
      (baseType.rename forwardRename).partialStrengthen? renameInverse
        = some baseType := by
    rw [Ty.partialStrengthen?_rename_some baseType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity baseType]
  have boundaryStrengthens :
      (boundaryWitness.rename forwardRename).partialStrengthen? renameInverse
        = some boundaryWitness := by
    rw [RawTerm.partialStrengthen?_rename_some boundaryWitness forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity boundaryWitness]
  split
  next noBaseTypeSuccess =>
    exact absurd (baseTypeStrengthens.symm.trans noBaseTypeSuccess)
      (by intro contra; cases contra)
  next targetBaseType baseTypeSuccess =>
    have baseTypeEq : targetBaseType = baseType :=
      Option.some.inj (baseTypeSuccess.symm.trans baseTypeStrengthens)
    subst baseTypeEq
    split
    next noBoundarySuccess =>
      exact absurd (boundaryStrengthens.symm.trans noBoundarySuccess)
        (by intro contra; cases contra)
    next targetBoundaryWitness boundarySuccess =>
      have boundaryEq : targetBoundaryWitness = boundaryWitness :=
        Option.some.inj (boundarySuccess.symm.trans boundaryStrengthens)
      subst boundaryEq
      split
      next noBaseValueSuccess =>
        exact absurd (baseIH.symm.trans noBaseValueSuccess)
          (by intro contra; cases contra)
      next baseValueResult baseValueSuccess =>
        have baseValueEq : baseValueResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              baseValue :=
          Option.some.inj (baseValueSuccess.symm.trans baseIH)
        subst baseValueEq
        split
        next noPartialSuccess =>
          exact absurd (partialIH.symm.trans noPartialSuccess)
            (by intro contra; cases contra)
        next partialResult partialSuccess =>
          have partialEq : partialResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                partialValue :=
            Option.some.inj (partialSuccess.symm.trans partialIH)
          subst partialEq
          rfl

/-- HoTT-special strength-T1 case: `Term.pathApp`.

Path application: 1 implicit Ty (carrierType) + 2 implicit RawTerm
(leftEndpoint, rightEndpoint) at outer `back`, + 2 Term IHs
(pathTerm at `Ty.path carrierType leftEndpoint rightEndpoint` +
intervalTerm at `Ty.interval`). -/
theorem strengthenTyped?_rename_eq_pathApp
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    (pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term sourceCtx Ty.interval intervalRaw)
    (pathIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming pathTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            pathTerm))
    (intervalIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming intervalTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            intervalTerm)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.pathApp (context := sourceCtx) modeIsUnivalent pathTerm
            intervalTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.pathApp (context := sourceCtx) modeIsUnivalent pathTerm
            intervalTerm)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have carrierStrengthens :
      (carrierType.rename forwardRename).partialStrengthen? renameInverse
        = some carrierType := by
    rw [Ty.partialStrengthen?_rename_some carrierType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierType]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse
        = some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact absurd (carrierStrengthens.symm.trans noCarrierSuccess)
      (by intro contra; cases contra)
  next targetCarrierType carrierSuccess =>
    have carrierEq : targetCarrierType = carrierType :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact absurd (leftStrengthens.symm.trans noLeftSuccess)
        (by intro contra; cases contra)
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact absurd (rightStrengthens.symm.trans noRightSuccess)
          (by intro contra; cases contra)
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noPathSuccess =>
          exact absurd (pathIH.symm.trans noPathSuccess)
            (by intro contra; cases contra)
        next pathResult pathSuccess =>
          have pathEq : pathResult =
              StrengtheningResult.fromRename forwardRename typedRenaming
                renameInverse renameInverseLeft renameInverseInjects
                pathTerm :=
            Option.some.inj (pathSuccess.symm.trans pathIH)
          subst pathEq
          split
          next noIntervalSuccess =>
            exact absurd (intervalIH.symm.trans noIntervalSuccess)
              (by intro contra; cases contra)
          next intervalResult intervalSuccess =>
            have intervalEq : intervalResult =
                StrengtheningResult.fromRename forwardRename typedRenaming
                  renameInverse renameInverseLeft renameInverseInjects
                  intervalTerm :=
              Option.some.inj (intervalSuccess.symm.trans intervalIH)
            subst intervalEq
            rfl

/-- HoTT-special strength-T1 case: `Term.codataUnfold`.

Codata constructor: 1 implicit Ty payload (outputType) at outer
`back` + 2 Term IHs (initialState at `stateType` + transition at
`Ty.arrow stateType outputType`).  `stateType` is also implicit but
the dispatcher only strengthens `outputType`. -/
theorem strengthenTyped?_rename_eq_codataUnfold
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    (initialState : Term sourceCtx stateType stateRaw)
    (transition : Term sourceCtx (Ty.arrow stateType outputType) transitionRaw)
    (stateIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming initialState)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            initialState))
    (transitionIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming transition)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            transition)) :
    partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.codataUnfold (context := sourceCtx) initialState transition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)
      = some (StrengtheningResult.fromRename forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects
          (Term.codataUnfold (context := sourceCtx) initialState
            transition)) := by
  dsimp only [Term.rename]
  unfold partialStrengthenTyped?
  have outputStrengthens :
      (outputType.rename forwardRename).partialStrengthen? renameInverse
        = some outputType := by
    rw [Ty.partialStrengthen?_rename_some outputType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity outputType]
  split
  next noOutputSuccess =>
    exact absurd (outputStrengthens.symm.trans noOutputSuccess)
      (by intro contra; cases contra)
  next targetOutputType outputSuccess =>
    have outputEq : targetOutputType = outputType :=
      Option.some.inj (outputSuccess.symm.trans outputStrengthens)
    subst outputEq
    split
    next noStateSuccess =>
      exact absurd (stateIH.symm.trans noStateSuccess)
        (by intro contra; cases contra)
    next stateResult stateSuccess =>
      have stateEq : stateResult =
          StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            initialState :=
        Option.some.inj (stateSuccess.symm.trans stateIH)
      subst stateEq
      split
      next noTransitionSuccess =>
        exact absurd (transitionIH.symm.trans noTransitionSuccess)
          (by intro contra; cases contra)
      next transitionResult transitionSuccess =>
        have transitionEq : transitionResult =
            StrengtheningResult.fromRename forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects
              transition :=
          Option.some.inj (transitionSuccess.symm.trans transitionIH)
        subst transitionEq
        rfl

end Term

end LeanFX2
