import LeanFX2.Term.StrengtheningImage.RenameImageTypeCodes

/-! # Term/StrengtheningImage/RenameImageHoTTStructured

Rename-image success bridges for HoTT, refinement, session, equivalence, and heterogeneous constructors.
-/

namespace LeanFX2

namespace Term

/-- T3 reverse-image bridge for `Term.idJ`. -/
theorem strengthenTyped?_rename_isSome_idJ
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
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseCase))
    (witnessIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            witness)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.idJ baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_idJ forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects baseCase witness
      baseIH witnessIH)

/-- T3 reverse-image bridge for `Term.oeqJ`. -/
theorem strengthenTyped?_rename_isSome_oeqJ
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
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseCase))
    (witnessIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            witness)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.oeqJ baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_oeqJ forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects baseCase witness
      baseIH witnessIH)

/-- T3 reverse-image bridge for `Term.idStrictRec`. -/
theorem strengthenTyped?_rename_isSome_idStrictRec
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
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    (baseCase : Term sourceCtx motiveType baseRaw)
    (witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseCase))
    (witnessIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            witness)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idStrictRec modeIsStrict baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_idStrictRec forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects modeIsStrict
      baseCase witness baseIH witnessIH)

/-- T3 reverse-image bridge for `Term.hcomp`. -/
theorem strengthenTyped?_rename_isSome_hcomp
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
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    (sidesValue : Term sourceCtx carrierType sidesRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming sidesValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            sidesValue))
    (capIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming capValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            capValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.hcomp modeIsUnivalent sidesValue capValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_hcomp forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects modeIsUnivalent
      sidesValue capValue sidesIH capIH)

/-- T3 reverse-image bridge for `Term.funextReflAtId`. -/
theorem strengthenTyped?_rename_isSome_funextReflAtId
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
    {domainType codomainType : Ty level sourceScope}
    (applyRaw : RawTerm (sourceScope + 1)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextReflAtId (context := sourceCtx) domainType codomainType
            applyRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_funextReflAtId forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects applyRaw)

/-- T3 reverse-image bridge for `Term.refineIntro`. -/
theorem strengthenTyped?_rename_isSome_refineIntro
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
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType valueRaw)
    (predicateProof : Term sourceCtx Ty.unit proofRaw)
    (baseIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming baseValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            baseValue))
    (proofIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming predicateProof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            predicateProof)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineIntro (context := sourceCtx) predicate baseValue
            predicateProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_refineIntro forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects predicate baseValue
      predicateProof baseIH proofIH)

/-- T3 reverse-image bridge for `Term.refineElim`. -/
theorem strengthenTyped?_rename_isSome_refineElim
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
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    (refinedValue : Term sourceCtx (Ty.refine baseType predicate) refinedRaw)
    (refinedIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming refinedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            refinedValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineElim (context := sourceCtx) (baseType := baseType)
            (predicate := predicate) refinedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_refineElim forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects refinedValue
      refinedIH)

/-- T3 reverse-image bridge for `Term.sessionSend`. -/
theorem strengthenTyped?_rename_isSome_sessionSend
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
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (payload : Term sourceCtx payloadType payloadRaw)
    (channelIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            channel))
    (payloadIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming payload)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            payload)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sessionSend (context := sourceCtx) protocolStep channel
            payload))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_sessionSend forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects protocolStep
      channel payload channelIH payloadIH)

/-- T3 reverse-image bridge for `Term.equivApp`. -/
theorem strengthenTyped?_rename_isSome_equivApp
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
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivApp (context := sourceCtx) equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_equivApp forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects equivTerm
      argumentTerm equivIH argumentIH)

/-- T3 reverse-image bridge for `Term.fst`. -/
theorem strengthenTyped?_rename_isSome_fst
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
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    (pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw)
    (pairIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming pairTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            pairTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.fst pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_fst forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects pairTerm pairIH)

/-- T3 reverse-image bridge for `Term.codataUnfold`. -/
theorem strengthenTyped?_rename_isSome_codataUnfold
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
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    (initialState : Term sourceCtx stateType stateRaw)
    (transition : Term sourceCtx (Ty.arrow stateType outputType) transitionRaw)
    (stateIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming initialState)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            initialState))
    (transitionIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming transition)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            transition)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.codataUnfold (context := sourceCtx) initialState transition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_codataUnfold forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects initialState
      transition stateIH transitionIH)

/-- T3 reverse-image bridge for `Term.equivApply`. -/
theorem strengthenTyped?_rename_isSome_equivApply
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
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw)
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.equivApply equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_equivApply forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects equivTerm
      argumentTerm equivIH argumentIH)

/-- T3 reverse-image bridge for `Term.uaToEquiv`. -/
theorem strengthenTyped?_rename_isSome_uaToEquiv
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
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    (proof : Term sourceCtx
      (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
      proofRaw)
    (proofIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming proof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            proof)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
            leftTy rightTy leftTyRaw rightTyRaw proof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_uaToEquiv forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerLevel
      innerLevelLt leftTy rightTy leftTyRaw rightTyRaw proof proofIH)

/-- T3 reverse-image bridge for `Term.uaIntroHet`. -/
theorem strengthenTyped?_rename_isSome_uaIntroHet
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
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (equivWitness : Term sourceCtx (Ty.equiv carrierA carrierB)
                       (RawTerm.equivIntro forwardRaw backwardRaw))
    (equivIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming equivWitness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            equivWitness)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
            carrierARaw carrierBRaw equivWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_uaIntroHet forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerLevel
      innerLevelLt carrierARaw carrierBRaw equivWitness equivIH)

/-- T3 reverse-image bridge for `Term.funextIntroHet`. -/
theorem strengthenTyped?_rename_isSome_funextIntroHet
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
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.funextIntroHet (context := sourceCtx) domainType codomainType
            applyARaw applyBRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_funextIntroHet forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects domainType
      codomainType applyARaw applyBRaw)

end Term

end LeanFX2
