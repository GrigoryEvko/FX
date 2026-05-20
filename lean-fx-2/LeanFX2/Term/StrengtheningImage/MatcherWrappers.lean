import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.MatcherSuccess

/-! # Term/StrengtheningImage/MatcherWrappers

Soundness lemmas for app-pattern wrappers around list, option, and either matchers.
-/

namespace LeanFX2

namespace Term

/-- Soundness of the App-pattern `partialStrengthenTypedListElim`
wrapper.  Cases the three subterm results, aligns each list/arrow type
shape via `Option.mapTwo`/`match` rewriting on the pivot
`elementSuccess`, and delegates to `_OfSuccess_sound` with the cascade
of `.termRenames` HEq witnesses. -/
theorem partialStrengthenTypedListElim_sound {mode : Mode} {level : Nat}
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
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {nilResult : StrengtheningResult strengthening nilBranch}
    {consResult : StrengtheningResult strengthening consBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (nilSound : StrengtheningSoundness nilResult)
    (consSound : StrengtheningSoundness consResult) :
    StrengtheningSoundness
      (partialStrengthenTypedListElim elementSuccess scrutineeResult
        nilResult consResult) := by
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
              exact partialStrengthenTypedListElimOfSuccess_sound
                (scrutinee := scrutinee) (nilBranch := nilBranch)
                (consBranch := consBranch)
                (elementSuccess := elementSuccess)
                (motiveSuccess := nilTypeStrengthens)
                (scrutineeRawStrengthens := scrutineeRawStrengthens)
                (nilRawStrengthens := nilRawStrengthens)
                (consRawStrengthens := consRawStrengthens)
                (scrutineeRawRenames := scrutineeRawRenames)
                (nilRawRenames := nilRawRenames)
                (consRawRenames := consRawRenames)
                scrutineeSound.termRenames nilSound.termRenames
                consSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedOptionMatch`
wrapper.  Sister of `partialStrengthenTypedListElim_sound`: same
single-pivot (`elementSuccess`) cascade over `Ty.optionType` and the
some-branch `Ty.arrow`. -/
theorem partialStrengthenTypedOptionMatch_sound {mode : Mode} {level : Nat}
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
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {noneResult : StrengtheningResult strengthening noneBranch}
    {someResult : StrengtheningResult strengthening someBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (noneSound : StrengtheningSoundness noneResult)
    (someSound : StrengtheningSoundness someResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionMatch elementSuccess scrutineeResult
        noneResult someResult) := by
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
              exact partialStrengthenTypedOptionMatchOfSuccess_sound
                (scrutinee := scrutinee) (noneBranch := noneBranch)
                (someBranch := someBranch)
                (elementSuccess := elementSuccess)
                (motiveSuccess := noneTypeStrengthens)
                (scrutineeRawStrengthens := scrutineeRawStrengthens)
                (noneRawStrengthens := noneRawStrengthens)
                (someRawStrengthens := someRawStrengthens)
                (scrutineeRawRenames := scrutineeRawRenames)
                (noneRawRenames := noneRawRenames)
                (someRawRenames := someRawRenames)
                scrutineeSound.termRenames noneSound.termRenames
                someSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEitherMatch`
wrapper.  Triple-pivot cascade (`leftSuccess`/`rightSuccess`/`motiveSuccess`)
threads through `Ty.eitherType` decomposition and both branch
`Ty.arrow` shapes. -/
theorem partialStrengthenTypedEitherMatch_sound {mode : Mode} {level : Nat}
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
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {leftResult : StrengtheningResult strengthening leftBranch}
    {rightResult : StrengtheningResult strengthening rightBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (leftSound : StrengtheningSoundness leftResult)
    (rightSound : StrengtheningSoundness rightResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEitherMatch leftSuccess rightSuccess
        motiveSuccess scrutineeResult leftResult rightResult) := by
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
              exact partialStrengthenTypedEitherMatchOfSuccess_sound
                (scrutinee := scrutinee) (leftBranch := leftBranch)
                (rightBranch := rightBranch)
                (leftSuccess := leftSuccess)
                (rightSuccess := rightSuccess)
                (motiveSuccess := motiveSuccess)
                (scrutineeRawStrengthens := scrutineeRawStrengthens)
                (leftRawStrengthens := leftRawStrengthens)
                (rightRawStrengthens := rightRawStrengthens)
                (scrutineeRawRenames := scrutineeRawRenames)
                (leftRawRenames := leftRawRenames)
                (rightRawRenames := rightRawRenames)
                scrutineeSound.termRenames leftSound.termRenames
                rightSound.termRenames

end Term

end LeanFX2
