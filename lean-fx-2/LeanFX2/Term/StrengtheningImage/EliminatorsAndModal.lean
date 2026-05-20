import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/EliminatorsAndModal

Soundness lemmas for natural eliminators and modal strengthening producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness for natural-number eliminator strengthening. -/
theorem partialStrengthenTypedNatElim_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {zeroResult : StrengtheningResult strengthening zeroBranch}
    {succResult : StrengtheningResult strengthening succBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (zeroSound : StrengtheningSoundness zeroResult)
    (succSound : StrengtheningSoundness succResult) :
    StrengtheningSoundness
      (partialStrengthenTypedNatElim scrutineeResult zeroResult
        succResult) := by
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
              refine ⟨?_⟩
              dsimp [partialStrengthenTypedNatElim,
                  StrengtheningResult.renamedTarget]
                at scrutineeSound zeroSound succSound ⊢
              exact Term.natElim_HEq_congr zeroTypeRenames
                scrutineeRawRenames zeroRawRenames succRawRenames
                scrutineeSound.termRenames zeroSound.termRenames
                succSound.termRenames

/-- Soundness for natural-number recursor strengthening. -/
theorem partialStrengthenTypedNatRec_sound {mode : Mode} {level : Nat}
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
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {zeroResult : StrengtheningResult strengthening zeroBranch}
    {succResult : StrengtheningResult strengthening succBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (zeroSound : StrengtheningSoundness zeroResult)
    (succSound : StrengtheningSoundness succResult) :
    StrengtheningSoundness
      (partialStrengthenTypedNatRec scrutineeResult zeroResult
        succResult) := by
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
              refine ⟨?_⟩
              dsimp [partialStrengthenTypedNatRec,
                  StrengtheningResult.renamedTarget]
                at scrutineeSound zeroSound succSound ⊢
              exact Term.natRec_HEq_congr zeroTypeRenames
                scrutineeRawRenames zeroRawRenames succRawRenames
                scrutineeSound.termRenames zeroSound.termRenames
                succSound.termRenames

/-- Soundness for modal-introduction strengthening. -/
theorem partialStrengthenTypedModIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    {innerResult : StrengtheningResult strengthening innerTerm}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedModIntro innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedModIntro,
          StrengtheningResult.renamedTarget] at innerSound ⊢
      exact Term.modIntro_HEq_congr typeRenames rawRenames
        innerSound.termRenames

/-- Soundness for modal-elimination strengthening. -/
theorem partialStrengthenTypedModElim_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    {innerResult : StrengtheningResult strengthening innerTerm}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedModElim innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedModElim,
          StrengtheningResult.renamedTarget] at innerSound ⊢
      exact Term.modElim_HEq_congr typeRenames rawRenames
        innerSound.termRenames

/-- Soundness for modal-subsumption strengthening. -/
theorem partialStrengthenTypedSubsume_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    {innerResult : StrengtheningResult strengthening innerTerm}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedSubsume innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedSubsume,
          StrengtheningResult.renamedTarget] at innerSound ⊢
      exact Term.subsume_HEq_congr typeRenames rawRenames
        innerSound.termRenames

end Term

end LeanFX2
