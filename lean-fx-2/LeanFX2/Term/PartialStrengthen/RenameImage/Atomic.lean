import LeanFX2.Term.PartialStrengthen.RenameImage.Core

/-! # Term/PartialStrengthen/RenameImage/Atomic

Rename-image T1 equations for closed and parametric atomic term cases.
-/

namespace LeanFX2

namespace Term

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
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  dsimp only [Term.rename, partialStrengthenTyped?]
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
  dsimp only [Term.rename, partialStrengthenTyped?]
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

end Term

end LeanFX2
