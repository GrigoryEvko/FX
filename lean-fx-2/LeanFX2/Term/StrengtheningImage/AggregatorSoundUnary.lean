import LeanFX2.Term.StrengtheningImage.AggregatorSoundCore

/-! # Term/StrengtheningImage/AggregatorSoundUnary

Aggregator-soundness instances for unary and single-child structured constructors.
-/

namespace LeanFX2

namespace Term

/-- Headline aggregator soundness at the `Term.natSucc` arm.  1-IH
unary constructor over `Ty.nat`. -/
theorem isAggregatorSound_natSucc {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {predecessorRaw : RawTerm sourceScope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (predecessorAggregator : IsAggregatorSound predecessor) :
    IsAggregatorSound (Term.natSucc (predecessor := predecessor)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atNatSucc_imp_sound strengthening
    (predecessorAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.optionSome` arm.
1-IH unary constructor over a parametric `elementType`. -/
theorem isAggregatorSound_optionSome {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueAggregator : IsAggregatorSound valueTerm) :
    IsAggregatorSound (Term.optionSome (valueTerm := valueTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOptionSome_imp_sound strengthening
    (valueAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.modIntro` arm.  1-IH
modal introduction (8-modality dispatch). -/
theorem isAggregatorSound_modIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerAggregator : IsAggregatorSound innerTerm) :
    IsAggregatorSound (Term.modIntro (innerTerm := innerTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atModIntro_imp_sound strengthening
    (innerAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.modElim` arm.  1-IH
modal elimination. -/
theorem isAggregatorSound_modElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerAggregator : IsAggregatorSound innerTerm) :
    IsAggregatorSound (Term.modElim (innerTerm := innerTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atModElim_imp_sound strengthening
    (innerAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.subsume` arm.  1-IH
mode-subsumption. -/
theorem isAggregatorSound_subsume {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerAggregator : IsAggregatorSound innerTerm) :
    IsAggregatorSound (Term.subsume (innerTerm := innerTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSubsume_imp_sound strengthening
    (innerAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.eitherInl` arm.
1-IH plus internal `rightType` strengthening (handled inside the
leaf). -/
theorem isAggregatorSound_eitherInl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueAggregator : IsAggregatorSound valueTerm) :
    IsAggregatorSound
      (Term.eitherInl (rightType := rightType)
        (valueTerm := valueTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEitherInl_imp_sound strengthening
    (valueAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.eitherInr` arm.
Mirrors `eitherInl` with the unused side carried as `leftType`. -/
theorem isAggregatorSound_eitherInr {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueAggregator : IsAggregatorSound valueTerm) :
    IsAggregatorSound
      (Term.eitherInr (leftType := leftType)
        (valueTerm := valueTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEitherInr_imp_sound strengthening
    (valueAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.recordIntro` arm.
1-IH single-field record introduction. -/
theorem isAggregatorSound_recordIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (fieldAggregator : IsAggregatorSound firstField) :
    IsAggregatorSound
      (Term.recordIntro (firstField := firstField)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atRecordIntro_imp_sound strengthening
    (fieldAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.recordProj` arm.
1-IH single-field record projection. -/
theorem isAggregatorSound_recordProj {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {recordValue :
      Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (recordAggregator : IsAggregatorSound recordValue) :
    IsAggregatorSound
      (Term.recordProj (recordValue := recordValue)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atRecordProj_imp_sound strengthening
    (recordAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.refineElim` arm.
1-IH refinement elimination. -/
theorem isAggregatorSound_refineElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (refinedAggregator : IsAggregatorSound refinedValue) :
    IsAggregatorSound (Term.refineElim refinedValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atRefineElim_imp_sound strengthening
    (refinedAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.cumulUp` arm.
1-IH universe-cumulativity (positional level forwarding plus the
inner type-code value IH). -/
theorem isAggregatorSound_cumulUp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeAggregator : IsAggregatorSound typeCode) :
    IsAggregatorSound
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atCumulUp_imp_sound lowerLevel
    higherLevel cumulMonotone levelLeLow levelLeHigh strengthening
    (codeAggregator strengthening) result success

end Term

end LeanFX2
