import LeanFX2.Term.StrengtheningImage.AggregatorTotalCore

/-! # Term/StrengtheningImage/AggregatorTotalUnary

Aggregator totality wrappers for one-IH non-binder constructors.
-/

namespace LeanFX2

namespace Term

/-! ## Wave T1: 1-IH non-binder totality wrappers (Term-only payload).

Each ctor below has a single typed recursive child and no dependent
`Ty` payload separately consulted by the dispatcher (the child's type
is either trivial — `Ty.nat` / `Ty.interval` — or only consulted via
the source term's typeStrengthens).  The proof unfolds the raw
dispatcher to extract the child's `RawTerm` strengthening witness,
synthesizes the child's `Ty` strengthening witness from the source
type's hypothesis, applies the child's `IsAggregatorTotal` IH, then
discharges the dispatcher's `none` branches as impossible. -/

/-- 1-IH non-binder totality: `Term.natSucc`.  Predecessor has type
`Ty.nat`; child type strengthening is trivially `rfl`. -/
theorem isAggregatorTotal_natSucc {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {predecessorRaw : RawTerm sourceScope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (predecessorTotal : IsAggregatorTotal predecessor) :
    IsAggregatorTotal (Term.natSucc (predecessor := predecessor)) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetPredRaw predRawSuccess =>
    have predTypeStrengthens :
        (Ty.nat : Ty level sourceScope).partialStrengthen?
            strengthening.back =
          some Ty.nat := rfl
    have predTotalCall :=
      predecessorTotal strengthening predTypeStrengthens predRawSuccess
    split
    · next predFails =>
        rw [predFails] at predTotalCall
        cases predTotalCall
    · rfl

/-- 1-IH non-binder totality: `Term.intervalOpp`.  Child has type
`Ty.interval`; child type strengthening is trivially `rfl`. -/
theorem isAggregatorTotal_intervalOpp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerTotal : IsAggregatorTotal innerValue) :
    IsAggregatorTotal (Term.intervalOpp (innerValue := innerValue)) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetInnerRaw innerRawSuccess =>
    have innerTypeStrengthens :
        (Ty.interval : Ty level sourceScope).partialStrengthen?
            strengthening.back =
          some Ty.interval := rfl
    have innerTotalCall :=
      innerTotal strengthening innerTypeStrengthens innerRawSuccess
    split
    · next innerFails =>
        rw [innerFails] at innerTotalCall
        cases innerTotalCall
    · rfl

/-- 1-IH non-binder totality: `Term.modIntro`.  Child type equals the
source type — the dispatcher recurses directly without splitting on
any type payload. -/
theorem isAggregatorTotal_modIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerTotal : IsAggregatorTotal innerTerm) :
    IsAggregatorTotal (Term.modIntro (innerTerm := innerTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetInnerRaw innerRawSuccess =>
    have innerTotalCall :=
      innerTotal strengthening typeStrengthens innerRawSuccess
    split
    · next innerFails =>
        rw [innerFails] at innerTotalCall
        cases innerTotalCall
    · rfl

/-- 1-IH non-binder totality: `Term.modElim`.  Same shape as
`modIntro` — child type equals source type. -/
theorem isAggregatorTotal_modElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerTotal : IsAggregatorTotal innerTerm) :
    IsAggregatorTotal (Term.modElim (innerTerm := innerTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetInnerRaw innerRawSuccess =>
    have innerTotalCall :=
      innerTotal strengthening typeStrengthens innerRawSuccess
    split
    · next innerFails =>
        rw [innerFails] at innerTotalCall
        cases innerTotalCall
    · rfl

/-- 1-IH non-binder totality: `Term.subsume`.  Same shape as
`modIntro` / `modElim` — child type equals source type. -/
theorem isAggregatorTotal_subsume {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerTotal : IsAggregatorTotal innerTerm) :
    IsAggregatorTotal (Term.subsume (innerTerm := innerTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetInnerRaw innerRawSuccess =>
    have innerTotalCall :=
      innerTotal strengthening typeStrengthens innerRawSuccess
    split
    · next innerFails =>
        rw [innerFails] at innerTotalCall
        cases innerTotalCall
    · rfl

/-- 1-IH non-binder totality: `Term.optionSome`.  Source type is
`Ty.optionType elementType`; child type is `elementType`.  Extract
elementType's strengthening witness from the source's `typeStrengthens`. -/
theorem isAggregatorTotal_optionSome {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueTotal : IsAggregatorTotal valueTerm) :
    IsAggregatorTotal (Term.optionSome (valueTerm := valueTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- Extract elementType's strengthening from typeStrengthens.
  unfold Ty.partialStrengthen? at typeStrengthens
  split at typeStrengthens
  · next strengthenedElement elementSuccess =>
      unfold partialStrengthenTyped?
      unfold RawTerm.partialStrengthen? at rawStrengthens
      unfold RawTerm.partialRename? at rawStrengthens
      split at rawStrengthens
      rotate_left
      · cases rawStrengthens
      next targetValueRaw valueRawSuccess =>
        have valueTotalCall :=
          valueTotal strengthening elementSuccess valueRawSuccess
        split
        · next valueFails =>
            rw [valueFails] at valueTotalCall
            cases valueTotalCall
        · rfl
  · next elementFails =>
      cases typeStrengthens

/-- 1-IH non-binder totality: `Term.eitherInl`.  Source type is
`Ty.eitherType leftType rightType`; child type is `leftType`.  Extract
leftType's strengthening from typeStrengthens via `Option.mapTwo_eq_some`. -/
theorem isAggregatorTotal_eitherInl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueTotal : IsAggregatorTotal valueTerm) :
    IsAggregatorTotal
      (Term.eitherInl (rightType := rightType) (valueTerm := valueTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨targetLeftType, _, leftSuccess, _, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetValueRaw valueRawSuccess =>
    have valueTotalCall :=
      valueTotal strengthening leftSuccess valueRawSuccess
    split
    · next rightFails =>
        -- The dispatcher splits on rightType first; we know rightType
        -- strengthens (by the second component of typeStrengthens).
        obtain ⟨_, _, _, rightSuccess, _⟩ :=
          Option.mapTwo_eq_some typeStrengthens
        rw [rightSuccess] at rightFails
        cases rightFails
    · next _ _ =>
        split
        · next valueFails =>
            rw [valueFails] at valueTotalCall
            cases valueTotalCall
        · rfl

/-- 1-IH non-binder totality: `Term.eitherInr`.  Source type is
`Ty.eitherType leftType rightType`; child type is `rightType`.  Mirror
of `eitherInl` with `leftType` swapped. -/
theorem isAggregatorTotal_eitherInr {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueTotal : IsAggregatorTotal valueTerm) :
    IsAggregatorTotal
      (Term.eitherInr (leftType := leftType) (valueTerm := valueTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨_, _, leftSuccess, rightSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetValueRaw valueRawSuccess =>
    have valueTotalCall :=
      valueTotal strengthening rightSuccess valueRawSuccess
    split
    · next leftFails =>
        rw [leftSuccess] at leftFails
        cases leftFails
    · next _ _ =>
        split
        · next valueFails =>
            rw [valueFails] at valueTotalCall
            cases valueTotalCall
        · rfl

/-- 1-IH non-binder totality: `Term.recordIntro`.  Source type is
`Ty.record singleFieldType`; child type is `singleFieldType`.  The
dispatcher does NOT split on the type payload — it recurses directly
on `firstField`.  Extract singleFieldType's strengthening from
typeStrengthens via the inner match arm. -/
theorem isAggregatorTotal_recordIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (firstTotal : IsAggregatorTotal firstField) :
    IsAggregatorTotal (Term.recordIntro (firstField := firstField)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold Ty.partialStrengthen? at typeStrengthens
  split at typeStrengthens
  · next strengthenedField fieldSuccess =>
      unfold partialStrengthenTyped?
      unfold RawTerm.partialStrengthen? at rawStrengthens
      unfold RawTerm.partialRename? at rawStrengthens
      split at rawStrengthens
      rotate_left
      · cases rawStrengthens
      next targetFirstRaw firstRawSuccess =>
        have firstTotalCall :=
          firstTotal strengthening fieldSuccess firstRawSuccess
        split
        · next fieldFails =>
            rw [fieldFails] at firstTotalCall
            cases firstTotalCall
        · rfl
  · next fieldFails =>
      cases typeStrengthens

/-- 1-IH non-binder totality: `Term.recordProj`.  Source type is
`singleFieldType`; child carries `Ty.record singleFieldType`.  The
dispatcher splits on `singleFieldType.partialStrengthen?` (which we
get from `typeStrengthens` directly since source type IS the field
type), then recurses. -/
theorem isAggregatorTotal_recordProj {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (recordTotal : IsAggregatorTotal recordValue) :
    IsAggregatorTotal (Term.recordProj (recordValue := recordValue)) := by
  intros _ _ strengthening targetType _ typeStrengthens rawStrengthens
  -- typeStrengthens : singleFieldType.partialStrengthen? back = some _
  -- recordValue's type is Ty.record singleFieldType; reconstruct
  -- its strengthening witness via the inner match.
  have recordTypeStrengthens :
      (Ty.record singleFieldType).partialStrengthen? strengthening.back =
        some (Ty.record targetType) := by
    show (match singleFieldType.partialStrengthen? strengthening.back with
          | some strengthenedField => some (Ty.record strengthenedField)
          | none => none) = some _
    rw [typeStrengthens]
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetRecordRaw recordRawSuccess =>
    have recordTotalCall :=
      recordTotal strengthening recordTypeStrengthens recordRawSuccess
    split
    · next fieldFails =>
        rw [typeStrengthens] at fieldFails
        cases fieldFails
    · next _ _ =>
        split
        · next recordFails =>
            rw [recordFails] at recordTotalCall
            cases recordTotalCall
        · rfl

/-- 1-IH non-binder totality: `Term.sessionRecv`.  Source type is
`Ty.session protocolStep`, child type identical; raw form
`RawTerm.sessionRecv channelRaw`.  The dispatcher splits on
`protocolStep.partialStrengthen?` (extractable from typeStrengthens'
Ty.session match), then recurses on channel. -/
theorem isAggregatorTotal_sessionRecv {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelTotal : IsAggregatorTotal channel) :
    IsAggregatorTotal (Term.sessionRecv (channel := channel)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- Extract protocolStep raw strengthens from typeStrengthens via case analysis.
  have protocolSuccessExists : ∃ targetProtocol,
      protocolStep.partialStrengthen? strengthening.back = some targetProtocol := by
    rcases hStep : protocolStep.partialStrengthen? strengthening.back with _ | tgt
    · simp only [Ty.partialStrengthen?, hStep] at typeStrengthens
      cases typeStrengthens
    · exact ⟨tgt, rfl⟩
  obtain ⟨targetProtocol, protocolSuccess⟩ := protocolSuccessExists
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetChannelRaw channelRawSuccess =>
    have channelTotalCall :=
      channelTotal strengthening typeStrengthens channelRawSuccess
    split
    · next protocolFails =>
        rw [protocolSuccess] at protocolFails
        cases protocolFails
    · next _ _ =>
        split
        · next channelFails =>
            rw [channelFails] at channelTotalCall
            cases channelTotalCall
        · rfl

end Term

end LeanFX2
