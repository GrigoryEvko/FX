import LeanFX2.Term.StrengtheningImage.RenameImageCastCore
import LeanFX2.Term.StrengtheningImage.RenameImageCastAdvanced
import LeanFX2.Term.StrengtheningImage.RenameImageCubicalEffect

/-! # Term/StrengtheningImage/RenameImageCastWrapped

Aggregate import for cast-wrapped, cubical, and effect rename-image bridges.
-/

namespace LeanFX2

namespace Term

private theorem option_isSome_false_of_eq_none
    {SomeType : Type} {optionValue : Option SomeType}
    (optionNone : optionValue = none)
    (optionIsSome : optionValue.isSome = true) :
    False := by
  rw [optionNone] at optionIsSome
  cases optionIsSome

private theorem lift_rename_self_some {sourceScope targetScope : Nat}
    (forwardRename : RawRenaming sourceScope targetScope)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition) :
    ∀ sourcePosition,
      renameInverse.lift (forwardRename.lift sourcePosition) =
        some sourcePosition := by
    intro sourcePosition
    rw [PartialRawRenaming.lift_rename_some renameInverseLeft sourcePosition,
      RawRenaming.identity_lift_pointwise sourcePosition]

private theorem ty_rename_strengthens {level sourceScope targetScope : Nat}
    (sourceType : Ty level sourceScope)
    (forwardRename : RawRenaming sourceScope targetScope)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition) :
    (sourceType.rename forwardRename).partialStrengthen? renameInverse =
      some sourceType := by
  rw [Ty.partialStrengthen?_rename_some sourceType forwardRename
    (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
    Ty.rename_identity sourceType]

private theorem raw_rename_strengthens {sourceScope targetScope : Nat}
    (sourceRaw : RawTerm sourceScope)
    (forwardRename : RawRenaming sourceScope targetScope)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition) :
    (sourceRaw.rename forwardRename).partialStrengthen? renameInverse =
      some sourceRaw := by
  rw [RawTerm.partialStrengthen?_rename_some sourceRaw forwardRename
    (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
    RawTerm.rename_identity sourceRaw]

private theorem partialStrengthenTyped?_isSome_of_strengthening_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    {firstStrengthening secondStrengthening :
      ContextStrengthening sourceCtx targetCtx}
    (strengtheningEq : firstStrengthening = secondStrengthening)
    (sourceIsSome :
      (partialStrengthenTyped? sourceTerm firstStrengthening).isSome =
        true) :
    (partialStrengthenTyped? sourceTerm secondStrengthening).isSome =
      true := by
  cases strengtheningEq
  exact sourceIsSome

private theorem strengthenTyped?_rename_isSome_fst_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming pairTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.fst pairTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have firstStrengthens :
      (firstType.rename forwardRename).partialStrengthen? renameInverse =
        some firstType := by
    rw [Ty.partialStrengthen?_rename_some firstType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity firstType]
  have secondStrengthens :
      (secondType.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift =
        some secondType := by
    rw [Ty.partialStrengthen?_rename_some secondType forwardRename.lift
      (@RawRenaming.identity sourceScope).lift renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      Ty.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) secondType,
      Ty.rename_identity secondType]
  split
  next noFirstSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noFirstSuccess
        (option_isSome_of_eq_some firstStrengthens))
  next targetFirstType firstSuccess =>
    have firstEq : targetFirstType = firstType :=
      Option.some.inj (firstSuccess.symm.trans firstStrengthens)
    subst firstEq
    split
    next noSecondSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noSecondSuccess
          (option_isSome_of_eq_some secondStrengthens))
    next targetSecondType secondSuccess =>
      have secondEq : targetSecondType = secondType :=
        Option.some.inj (secondSuccess.symm.trans secondStrengthens)
      subst secondEq
      split
      next noPairSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noPairSuccess pairIH)
      next pairResult pairSuccess =>
        rfl

private theorem strengthenTyped?_rename_isSome_idJ_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (witnessIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.idJ baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse =
        some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse =
        some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse =
        some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierSuccess
        (option_isSome_of_eq_some carrierStrengthens))
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noLeftSuccess
          (option_isSome_of_eq_some leftStrengthens))
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noRightSuccess
            (option_isSome_of_eq_some rightStrengthens))
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noBaseSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noBaseSuccess baseIH)
        next baseResult baseSuccess =>
          split
          next noWitnessSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noWitnessSuccess witnessIH)
          next witnessResult witnessSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_oeqJ_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (witnessIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.oeqJ baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse =
        some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse =
        some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse =
        some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierSuccess
        (option_isSome_of_eq_some carrierStrengthens))
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noLeftSuccess
          (option_isSome_of_eq_some leftStrengthens))
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noRightSuccess
            (option_isSome_of_eq_some rightStrengthens))
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noBaseSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noBaseSuccess baseIH)
        next baseResult baseSuccess =>
          split
          next noWitnessSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noWitnessSuccess witnessIH)
          next witnessResult witnessSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_idStrictRec_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming baseCase)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (witnessIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming witness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idStrictRec modeIsStrict baseCase witness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierStrengthens :
      (carrier.rename forwardRename).partialStrengthen? renameInverse =
        some carrier := by
    rw [Ty.partialStrengthen?_rename_some carrier forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrier]
  have leftStrengthens :
      (leftEndpoint.rename forwardRename).partialStrengthen? renameInverse =
        some leftEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some leftEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity leftEndpoint]
  have rightStrengthens :
      (rightEndpoint.rename forwardRename).partialStrengthen? renameInverse =
        some rightEndpoint := by
    rw [RawTerm.partialStrengthen?_rename_some rightEndpoint forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity rightEndpoint]
  split
  next noCarrierSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierSuccess
        (option_isSome_of_eq_some carrierStrengthens))
  next targetCarrier carrierSuccess =>
    have carrierEq : targetCarrier = carrier :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noLeftSuccess
          (option_isSome_of_eq_some leftStrengthens))
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noRightSuccess
            (option_isSome_of_eq_some rightStrengthens))
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noBaseSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noBaseSuccess baseIH)
        next baseResult baseSuccess =>
          split
          next noWitnessSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noWitnessSuccess witnessIH)
          next witnessResult witnessSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_hcomp_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming sidesValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (capIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming capValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.hcomp modeIsUnivalent sidesValue capValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  split
  next noSidesSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noSidesSuccess sidesIH)
  next sidesResult sidesSuccess =>
    split
    next noCapSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noCapSuccess capIH)
    next capResult capSuccess =>
      rfl

private theorem strengthenTyped?_rename_isSome_refineIntro_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming baseValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (proofIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming predicateProof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineIntro predicate baseValue predicateProof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have predicateStrengthens :
      (predicate.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift =
        some predicate := by
    rw [RawTerm.partialStrengthen?_rename_some predicate
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) predicate,
      RawTerm.rename_identity predicate]
  split
  next noPredicateSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noPredicateSuccess
        (option_isSome_of_eq_some predicateStrengthens))
  next targetPredicate predicateSuccess =>
    have predicateEq : targetPredicate = predicate :=
      Option.some.inj (predicateSuccess.symm.trans predicateStrengthens)
    subst predicateEq
    split
    next noBaseSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noBaseSuccess baseIH)
    next baseResult baseSuccess =>
      split
      next noProofSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noProofSuccess proofIH)
      next proofResult proofSuccess =>
        rfl

private theorem strengthenTyped?_rename_isSome_refineElim_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming refinedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refineElim (baseType := baseType) (predicate := predicate)
            refinedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have baseStrengthens :
      (baseType.rename forwardRename).partialStrengthen? renameInverse =
        some baseType := by
    rw [Ty.partialStrengthen?_rename_some baseType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity baseType]
  have predicateStrengthens :
      (predicate.rename forwardRename.lift).partialStrengthen?
          renameInverse.lift =
        some predicate := by
    rw [RawTerm.partialStrengthen?_rename_some predicate
      forwardRename.lift (@RawRenaming.identity sourceScope).lift
      renameInverse.lift
      (PartialRawRenaming.lift_rename_some renameInverseLeft),
      RawTerm.rename_pointwise
        (@RawRenaming.identity_lift_pointwise sourceScope) predicate,
      RawTerm.rename_identity predicate]
  split
  next noBaseSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noBaseSuccess
        (option_isSome_of_eq_some baseStrengthens))
  next targetBaseType baseSuccess =>
    have baseEq : targetBaseType = baseType :=
      Option.some.inj (baseSuccess.symm.trans baseStrengthens)
    subst baseEq
    split
    next noPredicateSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noPredicateSuccess
          (option_isSome_of_eq_some predicateStrengthens))
    next targetPredicate predicateSuccess =>
      have predicateEq : targetPredicate = predicate :=
        Option.some.inj (predicateSuccess.symm.trans predicateStrengthens)
      subst predicateEq
      split
      next noRefinedSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noRefinedSuccess refinedIH)
      next refinedResult refinedSuccess =>
        rfl

private theorem strengthenTyped?_rename_isSome_codataUnfold_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming initialState)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (transitionIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming transition)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.codataUnfold initialState transition))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have outputStrengthens :
      (outputType.rename forwardRename).partialStrengthen? renameInverse =
        some outputType := by
    rw [Ty.partialStrengthen?_rename_some outputType forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity outputType]
  split
  next noOutputSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noOutputSuccess
        (option_isSome_of_eq_some outputStrengthens))
  next targetOutputType outputSuccess =>
    have outputEq : targetOutputType = outputType :=
      Option.some.inj (outputSuccess.symm.trans outputStrengthens)
    subst outputEq
    split
    next noStateSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noStateSuccess stateIH)
    next stateResult stateSuccess =>
      split
      next noTransitionSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noTransitionSuccess transitionIH)
      next transitionResult transitionSuccess =>
        rfl

private theorem strengthenTyped?_rename_isSome_sessionSend_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (payloadIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming payload)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sessionSend protocolStep channel payload))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have protocolStrengthens :
      (protocolStep.rename forwardRename).partialStrengthen? renameInverse =
        some protocolStep := by
    rw [RawTerm.partialStrengthen?_rename_some protocolStep forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity protocolStep]
  split
  next noProtocolSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noProtocolSuccess
        (option_isSome_of_eq_some protocolStrengthens))
  next targetProtocol protocolSuccess =>
    have protocolEq : targetProtocol = protocolStep :=
      Option.some.inj (protocolSuccess.symm.trans protocolStrengthens)
    subst protocolEq
    split
    next noChannelSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noChannelSuccess channelIH)
    next channelResult channelSuccess =>
      split
      next noPayloadSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noPayloadSuccess payloadIH)
      next payloadResult payloadSuccess =>
        rfl

private theorem strengthenTyped?_rename_isSome_equivApp_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (argumentIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.equivApp equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierAStrengthens :
      (carrierA.rename forwardRename).partialStrengthen? renameInverse =
        some carrierA := by
    rw [Ty.partialStrengthen?_rename_some carrierA forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierA]
  have carrierBStrengthens :
      (carrierB.rename forwardRename).partialStrengthen? renameInverse =
        some carrierB := by
    rw [Ty.partialStrengthen?_rename_some carrierB forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity carrierB]
  split
  next noCarrierASuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierASuccess
        (option_isSome_of_eq_some carrierAStrengthens))
  next targetCarrierA carrierASuccess =>
      have carrierAEq : targetCarrierA = carrierA :=
        Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
      subst carrierAEq
      split
      next noCarrierBSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noCarrierBSuccess
            (option_isSome_of_eq_some carrierBStrengthens))
      next targetCarrierB carrierBSuccess =>
        have carrierBEq : targetCarrierB = carrierB :=
          Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
        subst carrierBEq
        split
        next noEquivSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noEquivSuccess equivIH)
        next equivResult equivSuccess =>
          split
          next noArgumentSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noArgumentSuccess argumentIH)
          next argumentResult argumentSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_pathApp_of_childIsSome
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
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    (pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term sourceCtx Ty.interval intervalRaw)
    (pathIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming pathTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (intervalIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming intervalTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.pathApp modeIsUnivalent pathTerm intervalTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierStrengthens :=
    ty_rename_strengthens carrierType forwardRename renameInverse
      renameInverseLeft
  have leftStrengthens :=
    raw_rename_strengthens leftEndpoint forwardRename renameInverse
      renameInverseLeft
  have rightStrengthens :=
    raw_rename_strengthens rightEndpoint forwardRename renameInverse
      renameInverseLeft
  split
  next noCarrierSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierSuccess
        (option_isSome_of_eq_some carrierStrengthens))
  next targetCarrierType carrierSuccess =>
    have carrierEq : targetCarrierType = carrierType :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noLeftSuccess
          (option_isSome_of_eq_some leftStrengthens))
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noRightSuccess
            (option_isSome_of_eq_some rightStrengthens))
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noPathSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noPathSuccess pathIH)
        next pathResult pathSuccess =>
          split
          next noIntervalSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noIntervalSuccess intervalIH)
          next intervalResult intervalSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_glueIntro_of_childIsSome
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
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType baseRaw)
    (partialValue : Term sourceCtx baseType partialRaw)
    (baseIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming baseValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (partialIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming partialValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have baseTypeStrengthens :=
    ty_rename_strengthens baseType forwardRename renameInverse renameInverseLeft
  have boundaryStrengthens :=
    raw_rename_strengthens boundaryWitness forwardRename renameInverse
      renameInverseLeft
  split
  next noBaseTypeSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noBaseTypeSuccess
        (option_isSome_of_eq_some baseTypeStrengthens))
  next targetBaseType baseTypeSuccess =>
    have baseTypeEq : targetBaseType = baseType :=
      Option.some.inj (baseTypeSuccess.symm.trans baseTypeStrengthens)
    subst baseTypeEq
    split
    next noBoundarySuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noBoundarySuccess
          (option_isSome_of_eq_some boundaryStrengthens))
    next targetBoundaryWitness boundarySuccess =>
      have boundaryEq : targetBoundaryWitness = boundaryWitness :=
        Option.some.inj (boundarySuccess.symm.trans boundaryStrengthens)
      subst boundaryEq
      split
      next noBaseSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noBaseSuccess baseIH)
      next baseResult baseSuccess =>
        split
        next noPartialSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noPartialSuccess partialIH)
        next partialResult partialSuccess =>
          rfl

private theorem strengthenTyped?_rename_isSome_transp_of_childIsSome
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
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term sourceCtx sourceType sourceRaw)
    (pathIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming typePath)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (sourceIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming sourceValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.transp modeIsUnivalent universeLevel universeLevelLt
            sourceType targetType sourceTypeRaw targetTypeRaw typePath
            sourceValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have sourceTypeStrengthens :=
    ty_rename_strengthens sourceType forwardRename renameInverse
      renameInverseLeft
  have targetTypeStrengthens :=
    ty_rename_strengthens targetType forwardRename renameInverse
      renameInverseLeft
  have sourceTypeRawStrengthens :=
    raw_rename_strengthens sourceTypeRaw forwardRename renameInverse
      renameInverseLeft
  have targetTypeRawStrengthens :=
    raw_rename_strengthens targetTypeRaw forwardRename renameInverse
      renameInverseLeft
  split
  next noSourceTypeSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noSourceTypeSuccess
        (option_isSome_of_eq_some sourceTypeStrengthens))
  next targetSourceType sourceTypeSuccess =>
    have sourceTypeEq : targetSourceType = sourceType :=
      Option.some.inj (sourceTypeSuccess.symm.trans sourceTypeStrengthens)
    subst sourceTypeEq
    split
    next noTargetTypeSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noTargetTypeSuccess
          (option_isSome_of_eq_some targetTypeStrengthens))
    next targetTargetType targetTypeSuccess =>
      have targetTypeEq : targetTargetType = targetType :=
        Option.some.inj (targetTypeSuccess.symm.trans targetTypeStrengthens)
      subst targetTypeEq
      split
      next noSourceTypeRawSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noSourceTypeRawSuccess
            (option_isSome_of_eq_some sourceTypeRawStrengthens))
      next targetSourceTypeRaw sourceTypeRawSuccess =>
        have sourceTypeRawEq : targetSourceTypeRaw = sourceTypeRaw :=
          Option.some.inj
            (sourceTypeRawSuccess.symm.trans sourceTypeRawStrengthens)
        subst sourceTypeRawEq
        split
        next noTargetTypeRawSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noTargetTypeRawSuccess
              (option_isSome_of_eq_some targetTypeRawStrengthens))
        next targetTargetTypeRaw targetTypeRawSuccess =>
          have targetTypeRawEq : targetTargetTypeRaw = targetTypeRaw :=
            Option.some.inj
              (targetTypeRawSuccess.symm.trans targetTypeRawStrengthens)
          subst targetTypeRawEq
          split
          next noPathSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noPathSuccess pathIH)
          next pathResult pathSuccess =>
            split
            next noSourceSuccess =>
              exact False.elim
                (option_isSome_false_of_eq_none noSourceSuccess sourceIH)
            next sourceResult sourceSuccess =>
              rfl

private theorem strengthenTyped?_rename_isSome_hcompPath_of_childIsSome
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
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    (sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming sidesPath)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (capIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming capValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
            sidesPath capValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierStrengthens :=
    ty_rename_strengthens carrierType forwardRename renameInverse
      renameInverseLeft
  have leftStrengthens :=
    raw_rename_strengthens leftEndpoint forwardRename renameInverse
      renameInverseLeft
  have rightStrengthens :=
    raw_rename_strengthens rightEndpoint forwardRename renameInverse
      renameInverseLeft
  split
  next noCarrierSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierSuccess
        (option_isSome_of_eq_some carrierStrengthens))
  next targetCarrierType carrierSuccess =>
    have carrierEq : targetCarrierType = carrierType :=
      Option.some.inj (carrierSuccess.symm.trans carrierStrengthens)
    subst carrierEq
    split
    next noLeftSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noLeftSuccess
          (option_isSome_of_eq_some leftStrengthens))
    next targetLeftEndpoint leftSuccess =>
      have leftEq : targetLeftEndpoint = leftEndpoint :=
        Option.some.inj (leftSuccess.symm.trans leftStrengthens)
      subst leftEq
      split
      next noRightSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noRightSuccess
            (option_isSome_of_eq_some rightStrengthens))
      next targetRightEndpoint rightSuccess =>
        have rightEq : targetRightEndpoint = rightEndpoint :=
          Option.some.inj (rightSuccess.symm.trans rightStrengthens)
        subst rightEq
        split
        next noSidesSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noSidesSuccess sidesIH)
        next sidesResult sidesSuccess =>
          split
          next noCapSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noCapSuccess capIH)
          next capResult capSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_effectPerform_of_childIsSome
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
    (effectTag : RawTerm sourceScope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    (operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw)
    (operationIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming operationTag)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (argumentsIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming arguments)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.effectPerform effectTag effectRow operationSignature
            canPerformOperation operationTag arguments))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have effectTagStrengthens :=
    raw_rename_strengthens effectTag forwardRename renameInverse
      renameInverseLeft
  have argumentCarrierStrengthens :=
    ty_rename_strengthens operationSignature.argumentCarrier forwardRename
      renameInverse renameInverseLeft
  have resultCarrierStrengthens :=
    ty_rename_strengthens operationSignature.resultCarrier forwardRename
      renameInverse renameInverseLeft
  split
  next noEffectTagSuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noEffectTagSuccess
        (option_isSome_of_eq_some effectTagStrengthens))
  next targetEffectTag effectTagSuccess =>
    have effectTagEq : targetEffectTag = effectTag :=
      Option.some.inj (effectTagSuccess.symm.trans effectTagStrengthens)
    subst effectTagEq
    split
    next noArgumentCarrierSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noArgumentCarrierSuccess
          (option_isSome_of_eq_some argumentCarrierStrengthens))
    next targetArgumentCarrier argumentCarrierSuccess =>
      have argumentCarrierEq :
          targetArgumentCarrier = operationSignature.argumentCarrier :=
        Option.some.inj
          (argumentCarrierSuccess.symm.trans argumentCarrierStrengthens)
      subst argumentCarrierEq
      split
      next noResultCarrierSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noResultCarrierSuccess
            (option_isSome_of_eq_some resultCarrierStrengthens))
      next targetResultCarrier resultCarrierSuccess =>
        have resultCarrierEq :
            targetResultCarrier = operationSignature.resultCarrier :=
          Option.some.inj
            (resultCarrierSuccess.symm.trans resultCarrierStrengthens)
        subst resultCarrierEq
        split
        next noOperationSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noOperationSuccess operationIH)
        next operationResult operationSuccess =>
          split
          next noArgumentsSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noArgumentsSuccess argumentsIH)
          next argumentsResult argumentsSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_uaIntroHet_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming equivWitness)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw
            equivWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierAStrengthens :=
    ty_rename_strengthens carrierA forwardRename renameInverse renameInverseLeft
  have carrierBStrengthens :=
    ty_rename_strengthens carrierB forwardRename renameInverse renameInverseLeft
  have carrierARawStrengthens :=
    raw_rename_strengthens carrierARaw forwardRename renameInverse
      renameInverseLeft
  have carrierBRawStrengthens :=
    raw_rename_strengthens carrierBRaw forwardRename renameInverse
      renameInverseLeft
  have forwardStrengthens :=
    raw_rename_strengthens forwardRaw forwardRename renameInverse
      renameInverseLeft
  have backwardStrengthens :=
    raw_rename_strengthens backwardRaw forwardRename renameInverse
      renameInverseLeft
  split
  next noCarrierASuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierASuccess
        (option_isSome_of_eq_some carrierAStrengthens))
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noCarrierBSuccess
          (option_isSome_of_eq_some carrierBStrengthens))
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noCarrierARawSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noCarrierARawSuccess
            (option_isSome_of_eq_some carrierARawStrengthens))
      next targetCarrierARaw carrierARawSuccess =>
        have carrierARawEq : targetCarrierARaw = carrierARaw :=
          Option.some.inj
            (carrierARawSuccess.symm.trans carrierARawStrengthens)
        subst carrierARawEq
        split
        next noCarrierBRawSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noCarrierBRawSuccess
              (option_isSome_of_eq_some carrierBRawStrengthens))
        next targetCarrierBRaw carrierBRawSuccess =>
          have carrierBRawEq : targetCarrierBRaw = carrierBRaw :=
            Option.some.inj
              (carrierBRawSuccess.symm.trans carrierBRawStrengthens)
          subst carrierBRawEq
          split
          next noForwardSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noForwardSuccess
                (option_isSome_of_eq_some forwardStrengthens))
          next targetForwardRaw forwardSuccess =>
            have forwardEq : targetForwardRaw = forwardRaw :=
              Option.some.inj (forwardSuccess.symm.trans forwardStrengthens)
            subst forwardEq
            split
            next noBackwardSuccess =>
              exact False.elim
                (option_isSome_false_of_eq_none noBackwardSuccess
                  (option_isSome_of_eq_some backwardStrengthens))
            next targetBackwardRaw backwardSuccess =>
              have backwardEq : targetBackwardRaw = backwardRaw :=
                Option.some.inj
                  (backwardSuccess.symm.trans backwardStrengthens)
              subst backwardEq
              split
              next noEquivSuccess =>
                exact False.elim
                  (option_isSome_false_of_eq_none noEquivSuccess equivIH)
              next equivResult equivSuccess =>
                rfl

private theorem strengthenTyped?_rename_isSome_uaToEquiv_of_childIsSome
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
    (proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw)
    (proofIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming proof)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw
            rightTyRaw proof))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have leftTyStrengthens :=
    ty_rename_strengthens leftTy forwardRename renameInverse renameInverseLeft
  have rightTyStrengthens :=
    ty_rename_strengthens rightTy forwardRename renameInverse renameInverseLeft
  have leftRawStrengthens :=
    raw_rename_strengthens leftTyRaw forwardRename renameInverse
      renameInverseLeft
  have rightRawStrengthens :=
    raw_rename_strengthens rightTyRaw forwardRename renameInverse
      renameInverseLeft
  split
  next noLeftTySuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noLeftTySuccess
        (option_isSome_of_eq_some leftTyStrengthens))
  next targetLeftTy leftTySuccess =>
    have leftTyEq : targetLeftTy = leftTy :=
      Option.some.inj (leftTySuccess.symm.trans leftTyStrengthens)
    subst leftTyEq
    split
    next noRightTySuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noRightTySuccess
          (option_isSome_of_eq_some rightTyStrengthens))
    next targetRightTy rightTySuccess =>
      have rightTyEq : targetRightTy = rightTy :=
        Option.some.inj (rightTySuccess.symm.trans rightTyStrengthens)
      subst rightTyEq
      split
      next noLeftRawSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noLeftRawSuccess
            (option_isSome_of_eq_some leftRawStrengthens))
      next targetLeftTyRaw leftRawSuccess =>
        have leftRawEq : targetLeftTyRaw = leftTyRaw :=
          Option.some.inj (leftRawSuccess.symm.trans leftRawStrengthens)
        subst leftRawEq
        split
        next noRightRawSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noRightRawSuccess
              (option_isSome_of_eq_some rightRawStrengthens))
        next targetRightTyRaw rightRawSuccess =>
          have rightRawEq : targetRightTyRaw = rightTyRaw :=
            Option.some.inj (rightRawSuccess.symm.trans rightRawStrengthens)
          subst rightRawEq
          split
          next noProofSuccess =>
            exact False.elim
              (option_isSome_false_of_eq_none noProofSuccess proofIH)
          next proofResult proofSuccess =>
            rfl

private theorem strengthenTyped?_rename_isSome_equivApply_of_childIsSome
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
      (partialStrengthenTyped?
          (Term.rename typedRenaming equivTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true)
    (argumentIH :
      (partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.equivApply equivTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true := by
  dsimp only [Term.rename, partialStrengthenTyped?]
  have carrierAStrengthens :=
    ty_rename_strengthens carrierA forwardRename renameInverse renameInverseLeft
  have carrierBStrengthens :=
    ty_rename_strengthens carrierB forwardRename renameInverse renameInverseLeft
  split
  next noCarrierASuccess =>
    exact False.elim
      (option_isSome_false_of_eq_none noCarrierASuccess
        (option_isSome_of_eq_some carrierAStrengthens))
  next targetCarrierA carrierASuccess =>
    have carrierAEq : targetCarrierA = carrierA :=
      Option.some.inj (carrierASuccess.symm.trans carrierAStrengthens)
    subst carrierAEq
    split
    next noCarrierBSuccess =>
      exact False.elim
        (option_isSome_false_of_eq_none noCarrierBSuccess
          (option_isSome_of_eq_some carrierBStrengthens))
    next targetCarrierB carrierBSuccess =>
      have carrierBEq : targetCarrierB = carrierB :=
        Option.some.inj (carrierBSuccess.symm.trans carrierBStrengthens)
      subst carrierBEq
      split
      next noEquivSuccess =>
        exact False.elim
          (option_isSome_false_of_eq_none noEquivSuccess equivIH)
      next equivResult equivSuccess =>
        split
        next noArgumentSuccess =>
          exact False.elim
            (option_isSome_false_of_eq_none noArgumentSuccess argumentIH)
        next argumentResult argumentSuccess =>
          rfl

/-- Unified T1 surface: every typed rename lies in the corresponding
strengthening image.

The theorem deliberately exposes only `.isSome`.  Eleven constructor
families are cast-wrapped, so their stable public statement is success
under `partialStrengthenTyped?`, not an exact `some
StrengtheningResult.fromRename` equation. -/
theorem strengthenTyped?_rename_isSome
    {mode : Mode} {level : Nat}
    {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) :
    ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
      (forwardRename : RawRenaming sourceScope targetScope)
      (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
      (renameInverse : PartialRawRenaming targetScope sourceScope)
      (renameInverseLeft :
        ∀ sourcePosition,
          renameInverse (forwardRename sourcePosition) = some sourcePosition)
      (renameInverseInjects :
        ∀ targetPosition sourcePosition,
          renameInverse targetPosition = some sourcePosition →
          targetPosition = forwardRename sourcePosition),
      (partialStrengthenTyped?
          (Term.rename typedRenaming sourceTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)).isSome =
        true := by
  induction sourceTerm with
  | var position =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_var forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects position
  | unit =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_unit forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects
  | lam body bodyIH =>
      rename_i sourceScopeHere sourceCtxHere domainType codomainType bodyRaw
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_lam
      intro targetDomainType domainSuccess
      have domainStrengthens :
          (domainType.rename forwardRename).partialStrengthen?
              renameInverse =
            some domainType := by
        rw [Ty.partialStrengthen?_rename_some domainType forwardRename
          (@RawRenaming.identity sourceScopeHere) renameInverse
          renameInverseLeft, Ty.rename_identity domainType]
      have targetDomainEq : targetDomainType = domainType :=
        Option.some.inj (domainSuccess.symm.trans domainStrengthens)
      subst targetDomainType
      exact
        partialStrengthenTyped?_isSome_of_typeCast
          (Term.rename (typedRenaming.lift domainType) body)
          (Ty.weaken_rename_commute forwardRename codomainType)
          ((ContextStrengthening.ofRenaming forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects).lift
            (domainType.rename forwardRename) domainType domainSuccess)
          (bodyIH (forwardRename := forwardRename.lift)
              (typedRenaming := typedRenaming.lift domainType)
              (renameInverse := renameInverse.lift)
              (renameInverseLeft :=
                lift_rename_self_some forwardRename renameInverse
                  renameInverseLeft)
              (renameInverseInjects :=
                PartialRawRenaming.lift_renamingInjectsBack
                  renameInverseInjects))
  | app functionTerm argumentTerm functionIH argumentIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_app_of_childIsSome
      · exact functionIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact argumentIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | lamPi body bodyIH =>
      rename_i sourceScopeHere sourceCtxHere domainType codomainType bodyRaw
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_lamPi
      intro targetDomainType domainSuccess
      have domainStrengthens :
          (domainType.rename forwardRename).partialStrengthen?
              renameInverse =
            some domainType := by
        rw [Ty.partialStrengthen?_rename_some domainType forwardRename
          (@RawRenaming.identity sourceScopeHere) renameInverse
          renameInverseLeft, Ty.rename_identity domainType]
      have targetDomainEq : targetDomainType = domainType :=
        Option.some.inj (domainSuccess.symm.trans domainStrengthens)
      subst targetDomainType
      exact
        bodyIH (forwardRename := forwardRename.lift)
          (typedRenaming := typedRenaming.lift domainType)
          (renameInverse := renameInverse.lift)
          (renameInverseLeft :=
            lift_rename_self_some forwardRename renameInverse
              renameInverseLeft)
          (renameInverseInjects :=
            PartialRawRenaming.lift_renamingInjectsBack renameInverseInjects)
  | appPi functionTerm argumentTerm functionIH argumentIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_appPi
      · exact functionIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact argumentIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | pair firstValue secondValue firstIH secondIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_pair
      · exact firstIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact secondIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | fst pairTerm pairIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_fst_of_childIsSome
      exact pairIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | snd pairTerm pairIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_snd
      exact pairIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | boolTrue =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_boolTrue forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects
  | boolFalse =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_boolFalse forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects
  | boolElim scrutinee thenBranch elseBranch scrutineeIH thenIH elseIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_boolElim
      · exact scrutineeIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact thenIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact elseIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | natZero =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_natZero forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects
  | natSucc predecessor predecessorIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_natSucc_of_childIsSome
      exact predecessorIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | natElim scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_natElim_of_childIsSome
      · exact scrutineeIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact zeroIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact succIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | natRec scrutinee zeroBranch succBranch scrutineeIH zeroIH succIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_natRec_of_childIsSome
      · exact scrutineeIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact zeroIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact succIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | listNil =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_listNil forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects
  | listCons headTerm tailTerm headIH tailIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_listCons_of_childIsSome
      · exact headIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact tailIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | listElim scrutinee nilBranch consBranch scrutineeIH nilIH consIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_listElim_of_childIsSome
      · exact scrutineeIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact nilIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact consIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | optionNone =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_optionNone forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
  | optionSome valueTerm valueIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_optionSome_of_childIsSome
      exact valueIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | optionMatch scrutinee noneBranch someBranch scrutineeIH noneIH someIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_optionMatch_of_childIsSome
      · exact scrutineeIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact noneIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact someIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | eitherInl valueTerm valueIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_eitherInl_of_childIsSome
      exact valueIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | eitherInr valueTerm valueIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_eitherInr_of_childIsSome
      exact valueIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | eitherMatch scrutinee leftBranch rightBranch scrutineeIH leftIH rightIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_eitherMatch_of_childIsSome
      · exact scrutineeIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact leftIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact rightIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | refl carrier rawWitness =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_refl forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects
  | idJ baseCase witness baseIH witnessIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_idJ_of_childIsSome
      · exact baseIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact witnessIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | oeqRefl carrier rawWitness =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_oeqRefl forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects
  | oeqJ baseCase witness baseIH witnessIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_oeqJ_of_childIsSome
      · exact baseIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact witnessIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw
      pointwiseProof pointwiseIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_oeqFunext
      exact pointwiseIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | idStrictRefl modeIsStrict carrier rawWitness =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_idStrictRefl forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
  | idStrictRec modeIsStrict baseCase witness baseIH witnessIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_idStrictRec_of_childIsSome
      · exact baseIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact witnessIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | modIntro innerTerm innerIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_modIntro_of_childIsSome
      exact innerIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | modElim innerTerm innerIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_modElim_of_childIsSome
      exact innerIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | subsume innerTerm innerIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_subsume_of_childIsSome
      exact innerIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | interval0 =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_interval0 forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
  | interval1 =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_interval1 forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
  | intervalOpp innerValue innerIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_intervalOpp_of_childIsSome
      exact innerIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | intervalMeet leftValue rightValue leftIH rightIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_intervalMeet_of_childIsSome
      · exact leftIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact rightIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | intervalJoin leftValue rightValue leftIH rightIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_intervalJoin_of_childIsSome
      · exact leftIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact rightIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body bodyIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_pathLam
      intro intervalSuccess
      exact
        partialStrengthenTyped?_isSome_of_typeCast
          (Term.rename (typedRenaming.lift Ty.interval) body)
          (Ty.weaken_rename_commute forwardRename carrierType)
          ((ContextStrengthening.ofRenaming forwardRename typedRenaming
              renameInverse renameInverseLeft renameInverseInjects).lift
            Ty.interval Ty.interval intervalSuccess)
          (bodyIH (forwardRename := forwardRename.lift)
              (typedRenaming := typedRenaming.lift Ty.interval)
              (renameInverse := renameInverse.lift)
              (renameInverseLeft :=
                lift_rename_self_some forwardRename renameInverse
                  renameInverseLeft)
              (renameInverseInjects :=
                PartialRawRenaming.lift_renamingInjectsBack
                  renameInverseInjects))
  | pathApp modeIsUnivalent pathTerm intervalTerm pathIH intervalIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_pathApp_of_childIsSome
        · exact pathIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
        · exact intervalIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
  | glueIntro modeIsUnivalent baseType boundaryWitness baseValue partialValue
        baseIH partialIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_glueIntro_of_childIsSome
        · exact baseIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
        · exact partialIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
  | glueElim modeIsUnivalent gluedValue gluedIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_glueElim_of_childIsSome
      exact gluedIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | transp modeIsUnivalent universeLevel universeLevelLt sourceType targetType
        sourceTypeRaw targetTypeRaw typePath sourceValue pathIH sourceIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_transp_of_childIsSome
        · exact pathIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
        · exact sourceIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
  | hcomp modeIsUnivalent sidesValue capValue sidesIH capIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_hcomp_of_childIsSome
      · exact sidesIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact capIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | hcompPath modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue
        sidesIH capIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_hcompPath_of_childIsSome
        · exact sidesIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
        · exact capIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
  | recordIntro firstField fieldIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_recordIntro_of_childIsSome
      exact fieldIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | recordProj recordValue recordIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_recordProj_of_childIsSome
      exact recordIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | refineIntro predicate baseValue predicateProof baseIH proofIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_refineIntro_of_childIsSome
      · exact baseIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact proofIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | refineElim refinedValue refinedIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_refineElim_of_childIsSome
      exact refinedIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | codataUnfold initialState transition stateIH transitionIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_codataUnfold_of_childIsSome
      · exact stateIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact transitionIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | codataDest codataValue codataIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_codataDest_of_childIsSome
      exact codataIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | sessionSend protocolStep channel payload channelIH payloadIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_sessionSend_of_childIsSome
      · exact channelIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact payloadIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | sessionRecv channel channelIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_sessionRecv_of_childIsSome
      exact channelIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | effectPerform effectTag effectRow operationSignature canPerformOperation
        operationTag arguments operationIH argumentsIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_effectPerform_of_childIsSome
        · exact operationIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
        · exact argumentsIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
  | universeCode innerLevel outerLevel cumulOk levelLe =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_universeCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        innerLevel outerLevel cumulOk levelLe
  | cumulUp lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh
      typeCode codeIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_cumulUp_of_childIsSome
      exact codeIH (forwardRename := forwardRename)
        (typedRenaming := typedRenaming) (renameInverse := renameInverse)
        (renameInverseLeft := renameInverseLeft)
        (renameInverseInjects := renameInverseInjects)
  | equivReflId carrier =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_equivReflId forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
  | funextRefl domainType codomainType applyRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_funextRefl forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        applyRaw
  | equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_equivReflIdAtId forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        innerLevel innerLevelLt
  | funextReflAtId domainType codomainType applyRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_funextReflAtId forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        applyRaw
  | equivIntroHet forward backward leftInv rightInv forwardIH backwardIH
      leftInvIH rightInvIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_equivIntroHet
      · exact forwardIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact backwardIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact leftInvIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact rightInvIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | equivApp equivTerm argumentTerm equivIH argumentIH =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      apply strengthenTyped?_rename_isSome_equivApp_of_childIsSome
      · exact equivIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
      · exact argumentIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness
        proofIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_uaIntroHet_of_childIsSome
        exact proofIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | funextIntroHet domainType codomainType applyARaw applyBRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_funextIntroHet forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        domainType codomainType applyARaw applyBRaw
  | arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_arrowCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        outerLevel levelLe domainCodeRaw codomainCodeRaw
  | piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_piTyCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        outerLevel levelLe domainCodeRaw codomainCodeRaw
  | sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_sigmaTyCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        outerLevel levelLe domainCodeRaw codomainCodeRaw
  | productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_productCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        outerLevel levelLe firstCodeRaw secondCodeRaw
  | sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_sumCode forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
        leftCodeRaw rightCodeRaw
  | listCode outerLevel levelLe elementCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_listCode forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
        elementCodeRaw
  | optionCode outerLevel levelLe elementCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_optionCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        outerLevel levelLe elementCodeRaw
  | eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_eitherCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        outerLevel levelLe leftCodeRaw rightCodeRaw
  | idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_idCode forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
        typeCodeRaw leftRaw rightRaw
  | equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
      intro targetScope targetCtx forwardRename typedRenaming renameInverse
        renameInverseLeft renameInverseInjects
      exact strengthenTyped?_rename_isSome_equivCode forwardRename
        typedRenaming renameInverse renameInverseLeft renameInverseInjects
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw
  | uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw rightTyRaw
        pathWitness proofIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_uaToEquiv_of_childIsSome
        exact proofIH (forwardRename := forwardRename)
          (typedRenaming := typedRenaming) (renameInverse := renameInverse)
          (renameInverseLeft := renameInverseLeft)
          (renameInverseInjects := renameInverseInjects)
  | equivApply equivWitness argument proofIH argumentIH =>
        intro targetScope targetCtx forwardRename typedRenaming renameInverse
          renameInverseLeft renameInverseInjects
        apply strengthenTyped?_rename_isSome_equivApply_of_childIsSome
        · exact proofIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)
        · exact argumentIH (forwardRename := forwardRename)
            (typedRenaming := typedRenaming) (renameInverse := renameInverse)
            (renameInverseLeft := renameInverseLeft)
            (renameInverseInjects := renameInverseInjects)

end Term

end LeanFX2
