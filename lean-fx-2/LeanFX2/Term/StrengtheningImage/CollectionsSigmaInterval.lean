import LeanFX2.Term.StrengtheningImage.Core.Base
import LeanFX2.Term.PartialStrengthen.Constructors.CollectionsAndSums
import LeanFX2.Term.PartialStrengthen.Constructors.ModalInterval
import LeanFX2.Term.PartialStrengthen.Constructors.SigmaRecordCodataSession
import LeanFX2.Term.HEqCongr.Compound.ApplicationsAndBinders
import LeanFX2.Term.HEqCongr.Compound.EliminatorsAndRecursive
import LeanFX2.Term.HEqCongr.Atomic.Base

/-! # Term/StrengtheningImage/CollectionsSigmaInterval

Soundness lemmas for collection constructors, Sigma projections, and interval operations.
-/

namespace LeanFX2

namespace Term

/-- Soundness for list-cons strengthening. -/
theorem partialStrengthenTypedListCons_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    {headResult : StrengtheningResult strengthening headTerm}
    {tailResult : StrengtheningResult strengthening tailTerm}
    (headSound : StrengtheningSoundness headResult)
    (tailSound : StrengtheningSoundness tailResult) :
    StrengtheningSoundness
      (partialStrengthenTypedListCons headResult tailResult) := by
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
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedListCons,
              StrengtheningResult.renamedTarget] at headSound tailSound ⊢
          exact Term.listCons_HEq_congr headTypeRenames headRawRenames
            tailRawRenames headSound.termRenames tailSound.termRenames

/-- Soundness for either-left injection strengthening. -/
theorem partialStrengthenTypedEitherInlOfRightType_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {valueResult : StrengtheningResult strengthening valueTerm}
    (valueSound : StrengtheningSoundness valueResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEitherInlOfRightType rightTypeStrengthens
        valueResult) := by
  cases valueResult with
  | mk targetLeftType targetValueRaw targetValueTerm valueTypeStrengthens
      valueRawStrengthens valueTypeRenames valueRawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedEitherInlOfRightType,
        StrengtheningResult.renamedTarget] at valueSound ⊢
      have rightTypeRenames :
          rightType = targetRightType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename rightType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetRightType rightTypeStrengthens
      exact Term.eitherInl_HEq_congr valueTypeRenames rightTypeRenames
        valueRawRenames valueSound.termRenames

/-- Soundness for either-right injection strengthening. -/
theorem partialStrengthenTypedEitherInrOfLeftType_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
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
    {valueResult : StrengtheningResult strengthening valueTerm}
    (valueSound : StrengtheningSoundness valueResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEitherInrOfLeftType leftTypeStrengthens
        valueResult) := by
  cases valueResult with
  | mk targetRightType targetValueRaw targetValueTerm valueTypeStrengthens
      valueRawStrengthens valueTypeRenames valueRawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedEitherInrOfLeftType,
        StrengtheningResult.renamedTarget] at valueSound ⊢
      have leftTypeRenames :
          leftType = targetLeftType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename leftType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetLeftType leftTypeStrengthens
      exact Term.eitherInr_HEq_congr leftTypeRenames valueTypeRenames
        valueRawRenames valueSound.termRenames

/-- Soundness for Sigma-pair strengthening. -/
theorem partialStrengthenTypedPair_sound {mode : Mode} {level : Nat}
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
    {firstResult : StrengtheningResult strengthening firstValue}
    {secondResult : StrengtheningResult strengthening secondValue}
    (firstSound : StrengtheningSoundness firstResult)
    (secondSound : StrengtheningSoundness secondResult) :
    StrengtheningSoundness
      (partialStrengthenTypedPair secondTypeStrengthens firstResult
        secondResult) := by
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
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedPair,
            StrengtheningResult.renamedTarget] at firstSound secondSound ⊢
          have secondTypeRenames :
              secondType =
                targetSecondType.rename strengthening.forward.lift :=
            Ty.partialStrengthen?_imp_rename secondType
              strengthening.forward.lift strengthening.back.lift
              (PartialRawRenaming.lift_renamingInjectsBack
                strengthening.injectsBack)
              targetSecondType secondTypeStrengthens
          have secondCastSound :
              HEq secondValue
                (Ty.subst0_rename_commute targetSecondType
                  targetFirstType targetFirstRaw strengthening.forward ▸
                  Term.rename strengthening.toTermRenaming
                    targetSecondTerm) :=
            have castSound :
                HEq
                  (Term.rename strengthening.toTermRenaming
                    targetSecondTerm)
                  (Ty.subst0_rename_commute targetSecondType
                    targetFirstType targetFirstRaw
                    strengthening.forward ▸
                    Term.rename strengthening.toTermRenaming
                      targetSecondTerm) := by
              exact heq_cast_left
                (motive := fun resultType =>
                  Term sourceCtx resultType
                    (targetSecondRaw.rename strengthening.forward))
                (Ty.subst0_rename_commute targetSecondType
                  targetFirstType targetFirstRaw strengthening.forward)
                (Term.rename strengthening.toTermRenaming
                  targetSecondTerm)
            HEq.trans secondSound.termRenames castSound
          exact Term.pair_HEq_congr firstTypeRenames secondTypeRenames
            firstRawRenames secondRawRenames firstSound.termRenames
            secondCastSound

/-- Soundness for Sigma first-projection strengthening. -/
theorem partialStrengthenTypedFst_sound {mode : Mode} {level : Nat}
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
    {pairResult : StrengtheningResult strengthening pairTerm}
    (pairSound : StrengtheningSoundness pairResult) :
    StrengtheningSoundness
      (partialStrengthenTypedFst firstSuccess secondSuccess
        pairResult) := by
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
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedFst,
        StrengtheningResult.renamedTarget] at pairSound ⊢
      have firstTypeRenames :
          firstType = targetFirstType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename firstType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetFirstType firstSuccess
      have secondTypeRenames :
          secondType = targetSecondType.rename
            strengthening.forward.lift :=
        Ty.partialStrengthen?_imp_rename secondType
          strengthening.forward.lift strengthening.back.lift
          (PartialRawRenaming.lift_renamingInjectsBack
            strengthening.injectsBack)
          targetSecondType secondSuccess
      exact Term.fst_HEq_congr firstTypeRenames
        secondTypeRenames rawRenames pairSound.termRenames

/-- Soundness for Sigma second-projection strengthening. -/
theorem partialStrengthenTypedSnd_sound {mode : Mode} {level : Nat}
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
    {pairResult : StrengtheningResult strengthening pairTerm}
    (pairSound : StrengtheningSoundness pairResult) :
    StrengtheningSoundness
      (partialStrengthenTypedSnd firstSuccess secondSuccess
        pairResult) := by
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
          (RawTerm.fst pairRaw).partialStrengthen? strengthening.back =
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
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedSnd,
        StrengtheningResult.renamedTarget] at pairSound ⊢
      have firstTypeRenames :
          firstType = targetFirstType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename firstType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetFirstType firstSuccess
      have secondTypeRenames :
          secondType = targetSecondType.rename
            strengthening.forward.lift :=
        Ty.partialStrengthen?_imp_rename secondType
          strengthening.forward.lift strengthening.back.lift
          (PartialRawRenaming.lift_renamingInjectsBack
            strengthening.injectsBack)
          targetSecondType secondSuccess
      have sndWithoutCast :
          HEq (Term.snd (secondType := secondType) pairTerm)
            (Term.snd
              (secondType := targetSecondType.rename
                strengthening.forward.lift)
              (Term.rename strengthening.toTermRenaming targetTerm)) :=
        Term.snd_HEq_congr firstTypeRenames secondTypeRenames
          rawRenames pairSound.termRenames
      have castSound :
          HEq
            (Term.snd (Term.rename strengthening.toTermRenaming targetTerm))
            ((Ty.subst0_rename_commute targetSecondType targetFirstType
              (RawTerm.fst targetRaw) strengthening.forward).symm ▸
              Term.snd
                (Term.rename strengthening.toTermRenaming targetTerm)) := by
        exact heq_cast_left
          (motive := fun resultType =>
            Term sourceCtx resultType
              ((RawTerm.snd targetRaw).rename strengthening.forward))
          (Ty.subst0_rename_commute targetSecondType targetFirstType
            (RawTerm.fst targetRaw) strengthening.forward).symm
          (Term.snd (Term.rename strengthening.toTermRenaming targetTerm))
      exact HEq.trans sndWithoutCast castSound

/-- Soundness for interval-negation strengthening. -/
theorem partialStrengthenTypedIntervalOpp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    {innerResult : StrengtheningResult strengthening innerValue}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIntervalOpp innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      cases typeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedIntervalOpp, StrengtheningResult.renamedTarget]
        at innerSound ⊢
      exact Term.intervalOpp_HEq_congr rawRenames
        innerSound.termRenames

/-- Soundness for interval-meet strengthening. -/
theorem partialStrengthenTypedIntervalMeet_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    {leftResult : StrengtheningResult strengthening leftValue}
    {rightResult : StrengtheningResult strengthening rightValue}
    (leftSound : StrengtheningSoundness leftResult)
    (rightSound : StrengtheningSoundness rightResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIntervalMeet leftResult rightResult) := by
  cases leftResult with
  | mk leftTargetType leftTargetRaw leftTargetTerm leftTypeStrengthens
      leftRawStrengthens leftTypeRenames leftRawRenames =>
      cases rightResult with
      | mk rightTargetType rightTargetRaw rightTargetTerm rightTypeStrengthens
          rightRawStrengthens rightTypeRenames rightRawRenames =>
          cases leftTypeStrengthens
          cases rightTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedIntervalMeet,
              StrengtheningResult.renamedTarget] at leftSound rightSound ⊢
          exact Term.intervalMeet_HEq_congr leftRawRenames rightRawRenames
            leftSound.termRenames rightSound.termRenames

/-- Soundness for interval-join strengthening. -/
theorem partialStrengthenTypedIntervalJoin_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    {leftResult : StrengtheningResult strengthening leftValue}
    {rightResult : StrengtheningResult strengthening rightValue}
    (leftSound : StrengtheningSoundness leftResult)
    (rightSound : StrengtheningSoundness rightResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIntervalJoin leftResult rightResult) := by
  cases leftResult with
  | mk leftTargetType leftTargetRaw leftTargetTerm leftTypeStrengthens
      leftRawStrengthens leftTypeRenames leftRawRenames =>
      cases rightResult with
      | mk rightTargetType rightTargetRaw rightTargetTerm rightTypeStrengthens
          rightRawStrengthens rightTypeRenames rightRawRenames =>
          cases leftTypeStrengthens
          cases rightTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedIntervalJoin,
              StrengtheningResult.renamedTarget] at leftSound rightSound ⊢
          exact Term.intervalJoin_HEq_congr leftRawRenames rightRawRenames
            leftSound.termRenames rightSound.termRenames

end Term

end LeanFX2
