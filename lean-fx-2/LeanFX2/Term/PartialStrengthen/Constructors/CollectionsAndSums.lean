import LeanFX2.Term.PartialStrengthen.Constructors.ApplicationAndBinders

/-! # Term/PartialStrengthen/Constructors/CollectionsAndSums

Typed partial-strengthening producers for list constructors and eliminators,
option matches, and either injections and matches.
-/

namespace LeanFX2

namespace Term

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

end Term

end LeanFX2
