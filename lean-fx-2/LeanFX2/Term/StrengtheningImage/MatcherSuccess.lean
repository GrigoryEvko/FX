import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive

/-! # Term/StrengtheningImage/MatcherSuccess

Soundness lemmas for explicit success branches of list, option, and either matchers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for the explicit success branch of list-eliminator
strengthening.  Pure term-mode construction — proof reduces under
`dsimp` without traversing the wrapper's internal option dispatch. -/
theorem partialStrengthenTypedListElimOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {targetScrutineeTerm :
      Term targetCtx (Ty.listType targetElementType) targetScrutineeRaw}
    {targetNilTerm : Term targetCtx targetMotiveType targetNilRaw}
    {targetConsTerm :
      Term targetCtx
        (Ty.arrow targetElementType
          (Ty.arrow (Ty.listType targetElementType) targetMotiveType))
        targetConsRaw}
    {elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType}
    {motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType}
    {scrutineeRawStrengthens :
      scrutineeRaw.partialStrengthen? strengthening.back =
        some targetScrutineeRaw}
    {nilRawStrengthens :
      nilRaw.partialStrengthen? strengthening.back = some targetNilRaw}
    {consRawStrengthens :
      consRaw.partialStrengthen? strengthening.back = some targetConsRaw}
    {scrutineeRawRenames :
      scrutineeRaw = targetScrutineeRaw.rename strengthening.forward}
    {nilRawRenames :
      nilRaw = targetNilRaw.rename strengthening.forward}
    {consRawRenames :
      consRaw = targetConsRaw.rename strengthening.forward}
    (scrutineeSound :
      HEq scrutinee
        (Term.rename strengthening.toTermRenaming targetScrutineeTerm))
    (nilSound :
      HEq nilBranch
        (Term.rename strengthening.toTermRenaming targetNilTerm))
    (consSound :
      HEq consBranch
        (Term.rename strengthening.toTermRenaming targetConsTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedListElimOfSuccess
        (scrutinee := scrutinee) (nilBranch := nilBranch)
        (consBranch := consBranch)
        targetScrutineeTerm targetNilTerm targetConsTerm
        elementSuccess motiveSuccess scrutineeRawStrengthens
        nilRawStrengthens consRawStrengthens scrutineeRawRenames
        nilRawRenames consRawRenames) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedListElimOfSuccess,
      StrengtheningResult.renamedTarget]
  have elementRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementSuccess
  have motiveRenames :
      motiveType = targetMotiveType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename motiveType strengthening.forward
      strengthening.back strengthening.injectsBack targetMotiveType
      motiveSuccess
  exact Term.listElim_HEq_congr elementRenames motiveRenames
    scrutineeRawRenames nilRawRenames consRawRenames scrutineeSound
    nilSound consSound

/-- Soundness for the explicit success branch of option-match
strengthening.  Mirrors `partialStrengthenTypedListElimOfSuccess_sound`. -/
theorem partialStrengthenTypedOptionMatchOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {targetScrutineeTerm :
      Term targetCtx (Ty.optionType targetElementType)
        targetScrutineeRaw}
    {targetNoneTerm : Term targetCtx targetMotiveType targetNoneRaw}
    {targetSomeTerm :
      Term targetCtx (Ty.arrow targetElementType targetMotiveType)
        targetSomeRaw}
    {elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType}
    {motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType}
    {scrutineeRawStrengthens :
      scrutineeRaw.partialStrengthen? strengthening.back =
        some targetScrutineeRaw}
    {noneRawStrengthens :
      noneRaw.partialStrengthen? strengthening.back = some targetNoneRaw}
    {someRawStrengthens :
      someRaw.partialStrengthen? strengthening.back = some targetSomeRaw}
    {scrutineeRawRenames :
      scrutineeRaw = targetScrutineeRaw.rename strengthening.forward}
    {noneRawRenames :
      noneRaw = targetNoneRaw.rename strengthening.forward}
    {someRawRenames :
      someRaw = targetSomeRaw.rename strengthening.forward}
    (scrutineeSound :
      HEq scrutinee
        (Term.rename strengthening.toTermRenaming targetScrutineeTerm))
    (noneSound :
      HEq noneBranch
        (Term.rename strengthening.toTermRenaming targetNoneTerm))
    (someSound :
      HEq someBranch
        (Term.rename strengthening.toTermRenaming targetSomeTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionMatchOfSuccess
        (scrutinee := scrutinee) (noneBranch := noneBranch)
        (someBranch := someBranch)
        targetScrutineeTerm targetNoneTerm targetSomeTerm
        elementSuccess motiveSuccess scrutineeRawStrengthens
        noneRawStrengthens someRawStrengthens scrutineeRawRenames
        noneRawRenames someRawRenames) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOptionMatchOfSuccess,
      StrengtheningResult.renamedTarget]
  have elementRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementSuccess
  have motiveRenames :
      motiveType = targetMotiveType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename motiveType strengthening.forward
      strengthening.back strengthening.injectsBack targetMotiveType
      motiveSuccess
  exact Term.optionMatch_HEq_congr elementRenames motiveRenames
    scrutineeRawRenames noneRawRenames someRawRenames scrutineeSound
    noneSound someSound

/-- Soundness for the explicit success branch of either-match
strengthening.  Mirrors `partialStrengthenTypedListElimOfSuccess_sound`. -/
theorem partialStrengthenTypedEitherMatchOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {targetLeftType targetRightType targetMotiveType :
      Ty level targetScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {targetScrutineeRaw targetLeftRaw targetRightRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    {targetScrutineeTerm :
      Term targetCtx (Ty.eitherType targetLeftType targetRightType)
        targetScrutineeRaw}
    {targetLeftTerm :
      Term targetCtx (Ty.arrow targetLeftType targetMotiveType)
        targetLeftRaw}
    {targetRightTerm :
      Term targetCtx (Ty.arrow targetRightType targetMotiveType)
        targetRightRaw}
    {leftSuccess :
      leftType.partialStrengthen? strengthening.back =
        some targetLeftType}
    {rightSuccess :
      rightType.partialStrengthen? strengthening.back =
        some targetRightType}
    {motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType}
    {scrutineeRawStrengthens :
      scrutineeRaw.partialStrengthen? strengthening.back =
        some targetScrutineeRaw}
    {leftRawStrengthens :
      leftRaw.partialStrengthen? strengthening.back = some targetLeftRaw}
    {rightRawStrengthens :
      rightRaw.partialStrengthen? strengthening.back =
        some targetRightRaw}
    {scrutineeRawRenames :
      scrutineeRaw = targetScrutineeRaw.rename strengthening.forward}
    {leftRawRenames :
      leftRaw = targetLeftRaw.rename strengthening.forward}
    {rightRawRenames :
      rightRaw = targetRightRaw.rename strengthening.forward}
    (scrutineeSound :
      HEq scrutinee
        (Term.rename strengthening.toTermRenaming targetScrutineeTerm))
    (leftSound :
      HEq leftBranch
        (Term.rename strengthening.toTermRenaming targetLeftTerm))
    (rightSound :
      HEq rightBranch
        (Term.rename strengthening.toTermRenaming targetRightTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedEitherMatchOfSuccess
        (scrutinee := scrutinee) (leftBranch := leftBranch)
        (rightBranch := rightBranch)
        targetScrutineeTerm targetLeftTerm targetRightTerm
        leftSuccess rightSuccess motiveSuccess
        scrutineeRawStrengthens leftRawStrengthens rightRawStrengthens
        scrutineeRawRenames leftRawRenames rightRawRenames) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEitherMatchOfSuccess,
      StrengtheningResult.renamedTarget]
  have leftRenames :
      leftType = targetLeftType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename leftType strengthening.forward
      strengthening.back strengthening.injectsBack targetLeftType
      leftSuccess
  have rightRenames :
      rightType = targetRightType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename rightType strengthening.forward
      strengthening.back strengthening.injectsBack targetRightType
      rightSuccess
  have motiveRenames :
      motiveType = targetMotiveType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename motiveType strengthening.forward
      strengthening.back strengthening.injectsBack targetMotiveType
      motiveSuccess
  exact Term.eitherMatch_HEq_congr leftRenames rightRenames motiveRenames
    scrutineeRawRenames leftRawRenames rightRawRenames scrutineeSound
    leftSound rightSound

end Term

end LeanFX2
