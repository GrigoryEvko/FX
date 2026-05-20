import LeanFX2.Term.PartialStrengthen.Constructors.Atomic

/-! # Term/PartialStrengthen/Constructors/BoolNatOption

Typed partial-strengthening producers for the nat, bool, and option
families.  The option constructor has one recursive child; the nat and
bool eliminators thread multiple recursive children through their motive
strengthening equations.
-/

namespace LeanFX2

namespace Term

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
    dsimp only [Ty.rename]
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

end Term

end LeanFX2
