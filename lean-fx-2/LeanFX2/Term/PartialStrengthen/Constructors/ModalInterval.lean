import LeanFX2.Term.PartialStrengthen.Constructors.BoolNatOption

/-! # Term/PartialStrengthen/Constructors/ModalInterval

Typed partial-strengthening producers for modal wrappers and interval
unary/binary constructors.
-/

namespace LeanFX2

namespace Term

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

end Term

end LeanFX2
