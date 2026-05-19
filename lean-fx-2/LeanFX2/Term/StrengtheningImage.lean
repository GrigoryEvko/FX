import LeanFX2.Term.TypedInversion
import LeanFX2.Term.HEqCongr
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

/-! # Term/StrengtheningImage — soundness of typed strengthening.

`StrengtheningResult` records the index-level content of a successful
typed partial strengthening: the recovered target type/raw and the
forward-renaming equations for those indices.  This module adds the
term-level semantic content as a parallel certificate: successful
strengthening re-renames the recovered target term back to the original
source term.

The parallel record keeps the existing computational dispatcher stable.
Recursive constructor soundness lemmas can be added incrementally without
forcing every `StrengtheningResult` producer to grow a new field at once.
-/

namespace LeanFX2

namespace Term

universe u v

/-- Term-level semantic soundness for a typed strengthening result.

The target term, renamed through the strengthening's forward morphism, is
heterogeneously equal to the source term.  Heterogeneous equality is the
right equality here because `StrengtheningResult.renamedTarget` carries
the renamed target indices, while the source term carries the original
indices; the record's `typeRenames` and `rawRenames` fields explain that
these indices are propositionally equal. -/
structure StrengtheningSoundness {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (result : StrengtheningResult strengthening sourceTerm) where
  termRenames : HEq sourceTerm result.renamedTarget

/-- Heterogeneous equality between a value and a cast of that same value
on the right.  This isolates the `Eq.rec` bookkeeping used by the variable
case of `Term.rename`. -/
theorem heq_cast_right {indexType : Sort u} {motive : indexType → Sort v}
    {firstIndex secondIndex : indexType}
    (indexEq : firstIndex = secondIndex)
    (value : motive secondIndex) :
    HEq value (indexEq ▸ value) := by
  cases indexEq
  rfl

/-- Heterogeneous equality between a value and a cast of that same value
on the left.  Dependent eliminators use this orientation when `Term.rename`
casts a constructor built at the pre-commuted `subst0` type into the
post-commuted type. -/
theorem heq_cast_left {indexType : Sort u} {motive : indexType → Sort v}
    {firstIndex secondIndex : indexType}
    (indexEq : firstIndex = secondIndex)
    (value : motive firstIndex) :
    HEq value (indexEq ▸ value) := by
  cases indexEq
  rfl

/-- Renaming a variable is heterogeneously equal to the variable at the
renamed position.  `Term.rename` casts this variable across the
`TermRenaming` proof; this lemma packages the cast proof once for
strengthening soundness. -/
theorem rename_var_heq {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (position : Fin sourceScope) :
    HEq (Term.var (context := targetCtx) (rho position))
      (Term.rename termRenaming (Term.var (context := sourceCtx) position)) := by
  change HEq (Term.var (context := targetCtx) (rho position))
    ((termRenaming position).symm ▸
      Term.var (context := targetCtx) (rho position))
  exact heq_cast_right
    (motive := fun variableType =>
      Term targetCtx variableType (RawTerm.var (rho position)))
    (termRenaming position).symm
    (Term.var (context := targetCtx) (rho position))

/-- Soundness for the surviving-variable strengthening producer. -/
theorem partialStrengthenTypedVarOfSurvives_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sourcePosition : Fin sourceScope)
    (targetPosition : Fin targetScope)
    (survives : strengthening.back sourcePosition = some targetPosition) :
    StrengtheningSoundness
      (partialStrengthenTypedVarOfSurvives strengthening sourcePosition
        targetPosition survives) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedVarOfSurvives]
  have positionEq : sourcePosition = strengthening.forward targetPosition :=
    strengthening.injectsBack sourcePosition targetPosition survives
  cases positionEq
  exact rename_var_heq strengthening.toTermRenaming targetPosition

/-- Soundness for closed unit strengthening. -/
theorem partialStrengthenTypedUnit_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedUnit strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed boolean-true strengthening. -/
theorem partialStrengthenTypedBoolTrue_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedBoolTrue strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed boolean-false strengthening. -/
theorem partialStrengthenTypedBoolFalse_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedBoolFalse strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed natural-zero strengthening. -/
theorem partialStrengthenTypedNatZero_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedNatZero strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed interval-zero strengthening. -/
theorem partialStrengthenTypedInterval0_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedInterval0 strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed interval-one strengthening. -/
theorem partialStrengthenTypedInterval1_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedInterval1 strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for list-nil strengthening at a strengthened element type. -/
theorem partialStrengthenTypedListNilOfType_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningSoundness
      (partialStrengthenTypedListNilOfType strengthening elementType
        targetElementType elementTypeStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedListNilOfType,
    StrengtheningResult.renamedTarget]
  have elementTypeRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementTypeStrengthens
  exact Term.listNil_HEq_congr elementTypeRenames

/-- Soundness for option-none strengthening at a strengthened element type. -/
theorem partialStrengthenTypedOptionNoneOfType_sound {mode : Mode}
    {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionNoneOfType strengthening elementType
        targetElementType elementTypeStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOptionNoneOfType,
    StrengtheningResult.renamedTarget]
  have elementTypeRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementTypeStrengthens
  exact Term.optionNone_HEq_congr elementTypeRenames

/-- Soundness for natural-successor strengthening. -/
theorem partialStrengthenTypedNatSucc_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {predecessorRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {predecessorResult : StrengtheningResult strengthening predecessor}
    (predecessorSound : StrengtheningSoundness predecessorResult) :
    StrengtheningSoundness
      (partialStrengthenTypedNatSucc predecessorResult) := by
  cases predecessorResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      cases typeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedNatSucc, StrengtheningResult.renamedTarget]
        at predecessorSound ⊢
      exact Term.natSucc_HEq_congr rawRenames
        predecessorSound.termRenames

/-- Soundness for option-some strengthening. -/
theorem partialStrengthenTypedOptionSome_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {valueTerm : Term sourceCtx elementType valueRaw}
    {valueResult : StrengtheningResult strengthening valueTerm}
    (valueSound : StrengtheningSoundness valueResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionSome valueResult) := by
  cases valueResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedOptionSome,
          StrengtheningResult.renamedTarget] at valueSound ⊢
      exact Term.optionSome_HEq_congr typeRenames rawRenames
        valueSound.termRenames

/-- Soundness for boolean eliminator strengthening. -/
theorem partialStrengthenTypedBoolElim_sound {mode : Mode} {level : Nat}
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
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {thenResult : StrengtheningResult strengthening thenBranch}
    {elseResult : StrengtheningResult strengthening elseBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (thenSound : StrengtheningSoundness thenResult)
    (elseSound : StrengtheningSoundness elseResult) :
    StrengtheningSoundness
      (partialStrengthenTypedBoolElim motiveStrengthens scrutineeResult
        thenResult elseResult) := by
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
              refine ⟨?_⟩
              dsimp [partialStrengthenTypedBoolElim,
                  StrengtheningResult.renamedTarget]
                at scrutineeSound thenSound elseSound ⊢
              have scrutineeTermRenames := scrutineeSound.termRenames
              have thenTermRenames := thenSound.termRenames
              have elseTermRenames := elseSound.termRenames
              dsimp [StrengtheningResult.renamedTarget] at scrutineeTermRenames
              dsimp [StrengtheningResult.renamedTarget] at thenTermRenames
              dsimp [StrengtheningResult.renamedTarget] at elseTermRenames
              have motiveRenames :
                  motiveType = targetMotiveType.rename
                    strengthening.forward.lift :=
                Ty.partialStrengthen?_imp_rename motiveType
                  strengthening.forward.lift strengthening.back.lift
                  (strengthening.lift Ty.bool Ty.bool rfl).injectsBack
                  targetMotiveType motiveStrengthens
              have thenCastSound :
                  HEq thenBranch
                    (Ty.subst0_rename_commute targetMotiveType Ty.bool
                      RawTerm.boolTrue strengthening.forward ▸
                    Term.rename strengthening.toTermRenaming
                      targetThenTerm) :=
                have castSound :
                    HEq
                      (Term.rename strengthening.toTermRenaming
                        targetThenTerm)
                      (Ty.subst0_rename_commute targetMotiveType Ty.bool
                        RawTerm.boolTrue strengthening.forward ▸
                      Term.rename strengthening.toTermRenaming
                        targetThenTerm) := by
                  exact heq_cast_left
                    (motive := fun branchType =>
                      Term sourceCtx branchType
                        (targetThenRaw.rename strengthening.forward))
                    (Ty.subst0_rename_commute targetMotiveType Ty.bool
                      RawTerm.boolTrue strengthening.forward)
                    (Term.rename strengthening.toTermRenaming
                      targetThenTerm)
                HEq.trans thenTermRenames castSound
              have elseCastSound :
                  HEq elseBranch
                    (Ty.subst0_rename_commute targetMotiveType Ty.bool
                      RawTerm.boolFalse strengthening.forward ▸
                    Term.rename strengthening.toTermRenaming
                      targetElseTerm) :=
                have castSound :
                    HEq
                      (Term.rename strengthening.toTermRenaming
                        targetElseTerm)
                      (Ty.subst0_rename_commute targetMotiveType Ty.bool
                        RawTerm.boolFalse strengthening.forward ▸
                      Term.rename strengthening.toTermRenaming
                        targetElseTerm) := by
                  exact heq_cast_left
                    (motive := fun branchType =>
                      Term sourceCtx branchType
                        (targetElseRaw.rename strengthening.forward))
                    (Ty.subst0_rename_commute targetMotiveType Ty.bool
                      RawTerm.boolFalse strengthening.forward)
                    (Term.rename strengthening.toTermRenaming
                      targetElseTerm)
                HEq.trans elseTermRenames castSound
              exact HEq.trans
                (Term.boolElim_HEq_congr motiveRenames
                  scrutineeRawRenames thenRawRenames elseRawRenames
                  scrutineeTermRenames thenCastSound elseCastSound)
                (heq_cast_left
                  (motive := fun resultType =>
                    Term sourceCtx resultType
                      ((RawTerm.boolElim targetScrutineeRaw targetThenRaw
                        targetElseRaw).rename strengthening.forward))
                  (Ty.subst0_rename_commute targetMotiveType Ty.bool
                    targetScrutineeRaw strengthening.forward).symm
                  (Term.boolElim
                    (motiveType := targetMotiveType.rename
                      strengthening.forward.lift)
                    (Term.rename strengthening.toTermRenaming
                      targetScrutineeTerm)
                    (Ty.subst0_rename_commute targetMotiveType Ty.bool
                      RawTerm.boolTrue strengthening.forward ▸
                    Term.rename strengthening.toTermRenaming
                      targetThenTerm)
                    (Ty.subst0_rename_commute targetMotiveType Ty.bool
                      RawTerm.boolFalse strengthening.forward ▸
                    Term.rename strengthening.toTermRenaming
                      targetElseTerm)))

/-- Soundness for the explicit success branch of non-dependent
application strengthening. -/
theorem partialStrengthenTypedAppOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {targetFunctionRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    {targetFunctionTerm :
      Term targetCtx (Ty.arrow targetDomainType targetCodomainType)
        targetFunctionRaw}
    {targetArgumentTerm :
      Term targetCtx targetDomainType targetArgumentRaw}
    {domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType}
    {codomainSuccess :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType}
    {functionRawStrengthens :
      functionRaw.partialStrengthen? strengthening.back =
        some targetFunctionRaw}
    {argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw}
    {functionRawRenames :
      functionRaw = targetFunctionRaw.rename strengthening.forward}
    {argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward}
    (functionSound :
      HEq functionTerm
        (Term.rename strengthening.toTermRenaming targetFunctionTerm))
    (argumentSound :
      HEq argumentTerm
        (Term.rename strengthening.toTermRenaming targetArgumentTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedAppOfSuccess
        (functionTerm := functionTerm) (argumentTerm := argumentTerm)
        targetFunctionTerm targetArgumentTerm domainSuccess codomainSuccess
        functionRawStrengthens argumentRawStrengthens functionRawRenames
        argumentRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedAppOfSuccess]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainSuccess
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCodomainType codomainSuccess
  exact Term.app_HEq_congr domainRenames codomainRenames
    functionRawRenames argumentRawRenames functionSound argumentSound

/-- Soundness for non-dependent application strengthening. -/
theorem partialStrengthenTypedApp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    {functionResult : StrengtheningResult strengthening functionTerm}
    {argumentResult : StrengtheningResult strengthening argumentTerm}
    (functionSound : StrengtheningSoundness functionResult)
    (argumentSound : StrengtheningSoundness argumentResult) :
    StrengtheningSoundness
      (partialStrengthenTypedApp domainSuccess codomainSuccess
        functionResult argumentResult) := by
  cases functionResult with
  | mk targetFunctionType targetFunctionRaw targetFunctionTerm
      functionTypeStrengthens functionRawStrengthens functionTypeRenames
      functionRawRenames =>
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back)
          Ty.arrow = some targetFunctionType at functionTypeStrengthens
      rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
      cases functionTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [domainSuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedAppOfSuccess_sound
            (functionSound := functionSound.termRenames)
            (argumentSound := argumentSound.termRenames)
            (domainSuccess := domainSuccess)
            (codomainSuccess := codomainSuccess)
            (functionRawStrengthens := functionRawStrengthens)
            (argumentRawStrengthens := argumentRawStrengthens)
            (functionRawRenames := functionRawRenames)
            (argumentRawRenames := argumentRawRenames)

/-- Soundness for the explicit success branch of dependent application
strengthening. -/
theorem partialStrengthenTypedAppPiOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {targetCodomainType : Ty level (targetScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {targetFunctionRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    {targetFunctionTerm :
      Term targetCtx (Ty.piTy targetDomainType targetCodomainType)
        targetFunctionRaw}
    {targetArgumentTerm :
      Term targetCtx targetDomainType targetArgumentRaw}
    {domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType}
    {codomainSuccess :
      codomainType.partialStrengthen? strengthening.back.lift =
        some targetCodomainType}
    {functionRawStrengthens :
      functionRaw.partialStrengthen? strengthening.back =
        some targetFunctionRaw}
    {argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw}
    {functionRawRenames :
      functionRaw = targetFunctionRaw.rename strengthening.forward}
    {argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward}
    (functionSound :
      HEq functionTerm
        (Term.rename strengthening.toTermRenaming targetFunctionTerm))
    (argumentSound :
      HEq argumentTerm
        (Term.rename strengthening.toTermRenaming targetArgumentTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedAppPiOfSuccess
        (functionTerm := functionTerm) (argumentTerm := argumentTerm)
        targetFunctionTerm targetArgumentTerm domainSuccess codomainSuccess
        functionRawStrengthens argumentRawStrengthens functionRawRenames
        argumentRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedAppPiOfSuccess]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainSuccess
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward.lift :=
    Ty.partialStrengthen?_imp_rename codomainType
      strengthening.forward.lift strengthening.back.lift
      (strengthening.lift domainType targetDomainType
        domainSuccess).injectsBack targetCodomainType codomainSuccess
  exact HEq.trans
    (Term.appPi_HEq_congr domainRenames codomainRenames
      functionRawRenames argumentRawRenames functionSound argumentSound)
    (heq_cast_left
      (motive := fun resultType =>
        Term sourceCtx resultType
          ((RawTerm.app targetFunctionRaw targetArgumentRaw).rename
            strengthening.forward))
      (Ty.subst0_rename_commute targetCodomainType targetDomainType
        targetArgumentRaw strengthening.forward).symm
      (Term.appPi
        (Term.rename strengthening.toTermRenaming targetFunctionTerm)
        (Term.rename strengthening.toTermRenaming targetArgumentTerm)))

/-- Soundness for dependent application strengthening. -/
theorem partialStrengthenTypedAppPi_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {targetCodomainType : Ty level (targetScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (domainSuccess :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainSuccess :
      codomainType.partialStrengthen? strengthening.back.lift =
        some targetCodomainType)
    {functionResult : StrengtheningResult strengthening functionTerm}
    {argumentResult : StrengtheningResult strengthening argumentTerm}
    (functionSound : StrengtheningSoundness functionResult)
    (argumentSound : StrengtheningSoundness argumentResult) :
    StrengtheningSoundness
      (partialStrengthenTypedAppPi domainSuccess codomainSuccess
        functionResult argumentResult) := by
  cases functionResult with
  | mk targetFunctionType targetFunctionRaw targetFunctionTerm
      functionTypeStrengthens functionRawStrengthens functionTypeRenames
      functionRawRenames =>
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          (codomainType.partialStrengthen? strengthening.back.lift)
          Ty.piTy = some targetFunctionType at functionTypeStrengthens
      rw [domainSuccess, codomainSuccess] at functionTypeStrengthens
      cases functionTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [domainSuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedAppPiOfSuccess_sound
            (functionSound := functionSound.termRenames)
            (argumentSound := argumentSound.termRenames)
            (domainSuccess := domainSuccess)
            (codomainSuccess := codomainSuccess)
            (functionRawStrengthens := functionRawStrengthens)
            (argumentRawStrengthens := argumentRawStrengthens)
            (functionRawRenames := functionRawRenames)
            (argumentRawRenames := argumentRawRenames)

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

/-- Soundness for closed universe-code strengthening.  Closed-leaf
producer: the producer carries no scope-dependent payload, so the
recovered target renames to the source structurally. -/
theorem partialStrengthenTypedUniverseCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    StrengtheningSoundness
      (partialStrengthenTypedUniverseCode strengthening innerLevel
        outerLevel cumulOk levelLe) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for arrow type-code strengthening: each schematic raw
payload survives the strengthening and the recovered target term
renames back to the source via `Term.arrowCode_HEq_congr`. -/
theorem partialStrengthenTypedArrowCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (targetDomainCodeRaw targetCodomainCodeRaw : RawTerm targetScope)
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back =
        some targetCodomainCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedArrowCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe domainCodeRaw codomainCodeRaw
        targetDomainCodeRaw targetCodomainCodeRaw
        domainStrengthens codomainStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedArrowCode, StrengtheningResult.renamedTarget]
  have domainRenames :
      domainCodeRaw =
        targetDomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename domainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainCodeRaw domainStrengthens
  have codomainRenames :
      codomainCodeRaw =
        targetCodomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename codomainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCodomainCodeRaw codomainStrengthens
  exact Term.arrowCode_HEq_congr outerLevel levelLe domainRenames
    codomainRenames

/-- Soundness for Π type-code strengthening: domain at the current
context, codomain under the lifted partial renaming. -/
theorem partialStrengthenTypedPiTyCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedPiTyCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe domainCodeRaw codomainCodeRaw
        targetDomainCodeRaw targetCodomainCodeRaw
        domainStrengthens codomainStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedPiTyCode, StrengtheningResult.renamedTarget]
  have domainRenames :
      domainCodeRaw =
        targetDomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename domainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainCodeRaw domainStrengthens
  have codomainRenames :
      codomainCodeRaw =
        targetCodomainCodeRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename codomainCodeRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetCodomainCodeRaw codomainStrengthens
  exact Term.piTyCode_HEq_congr outerLevel levelLe domainRenames
    codomainRenames

/-- Soundness for Σ type-code strengthening: domain at the current
context, codomain under the lifted partial renaming. -/
theorem partialStrengthenTypedSigmaTyCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (targetDomainCodeRaw : RawTerm targetScope)
    (targetCodomainCodeRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainCodeRaw.partialStrengthen? strengthening.back =
        some targetDomainCodeRaw)
    (codomainStrengthens :
      codomainCodeRaw.partialStrengthen? strengthening.back.lift =
        some targetCodomainCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedSigmaTyCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe domainCodeRaw codomainCodeRaw
        targetDomainCodeRaw targetCodomainCodeRaw
        domainStrengthens codomainStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedSigmaTyCode,
    StrengtheningResult.renamedTarget]
  have domainRenames :
      domainCodeRaw =
        targetDomainCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename domainCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainCodeRaw domainStrengthens
  have codomainRenames :
      codomainCodeRaw =
        targetCodomainCodeRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename codomainCodeRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetCodomainCodeRaw codomainStrengthens
  exact Term.sigmaTyCode_HEq_congr outerLevel levelLe domainRenames
    codomainRenames

/-- Soundness for product type-code strengthening. -/
theorem partialStrengthenTypedProductCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (targetFirstCodeRaw targetSecondCodeRaw : RawTerm targetScope)
    (firstStrengthens :
      firstCodeRaw.partialStrengthen? strengthening.back =
        some targetFirstCodeRaw)
    (secondStrengthens :
      secondCodeRaw.partialStrengthen? strengthening.back =
        some targetSecondCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedProductCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe firstCodeRaw secondCodeRaw
        targetFirstCodeRaw targetSecondCodeRaw
        firstStrengthens secondStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedProductCode,
    StrengtheningResult.renamedTarget]
  have firstRenames :
      firstCodeRaw = targetFirstCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename firstCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetFirstCodeRaw firstStrengthens
  have secondRenames :
      secondCodeRaw = targetSecondCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename secondCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetSecondCodeRaw secondStrengthens
  exact Term.productCode_HEq_congr outerLevel levelLe firstRenames
    secondRenames

/-- Soundness for sum type-code strengthening. -/
theorem partialStrengthenTypedSumCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedSumCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe leftCodeRaw rightCodeRaw
        targetLeftCodeRaw targetRightCodeRaw
        leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedSumCode, StrengtheningResult.renamedTarget]
  have leftRenames :
      leftCodeRaw = targetLeftCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftCodeRaw leftStrengthens
  have rightRenames :
      rightCodeRaw = targetRightCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightCodeRaw rightStrengthens
  exact Term.sumCode_HEq_congr outerLevel levelLe leftRenames rightRenames

/-- Soundness for list type-code strengthening. -/
theorem partialStrengthenTypedListCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedListCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe elementCodeRaw targetElementCodeRaw
        elementStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedListCode, StrengtheningResult.renamedTarget]
  have elementRenames :
      elementCodeRaw =
        targetElementCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename elementCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetElementCodeRaw elementStrengthens
  exact Term.listCode_HEq_congr outerLevel levelLe elementRenames

/-- Soundness for option type-code strengthening. -/
theorem partialStrengthenTypedOptionCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (targetElementCodeRaw : RawTerm targetScope)
    (elementStrengthens :
      elementCodeRaw.partialStrengthen? strengthening.back =
        some targetElementCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe elementCodeRaw targetElementCodeRaw
        elementStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOptionCode,
    StrengtheningResult.renamedTarget]
  have elementRenames :
      elementCodeRaw =
        targetElementCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename elementCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetElementCodeRaw elementStrengthens
  exact Term.optionCode_HEq_congr outerLevel levelLe elementRenames

/-- Soundness for either type-code strengthening. -/
theorem partialStrengthenTypedEitherCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (targetLeftCodeRaw targetRightCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftCodeRaw)
    (rightStrengthens :
      rightCodeRaw.partialStrengthen? strengthening.back =
        some targetRightCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedEitherCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe leftCodeRaw rightCodeRaw
        targetLeftCodeRaw targetRightCodeRaw
        leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEitherCode,
    StrengtheningResult.renamedTarget]
  have leftRenames :
      leftCodeRaw = targetLeftCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftCodeRaw leftStrengthens
  have rightRenames :
      rightCodeRaw = targetRightCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightCodeRaw rightStrengthens
  exact Term.eitherCode_HEq_congr outerLevel levelLe leftRenames
    rightRenames

/-- Soundness for identity type-code strengthening. -/
theorem partialStrengthenTypedIdCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (targetTypeCodeRaw targetLeftRaw targetRightRaw : RawTerm targetScope)
    (typeCodeStrengthens :
      typeCodeRaw.partialStrengthen? strengthening.back =
        some targetTypeCodeRaw)
    (leftStrengthens :
      leftRaw.partialStrengthen? strengthening.back =
        some targetLeftRaw)
    (rightStrengthens :
      rightRaw.partialStrengthen? strengthening.back =
        some targetRightRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedIdCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe typeCodeRaw leftRaw rightRaw
        targetTypeCodeRaw targetLeftRaw targetRightRaw
        typeCodeStrengthens leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedIdCode, StrengtheningResult.renamedTarget]
  have typeCodeRenames :
      typeCodeRaw = targetTypeCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename typeCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetTypeCodeRaw typeCodeStrengthens
  have leftRenames :
      leftRaw = targetLeftRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftRaw leftStrengthens
  have rightRenames :
      rightRaw = targetRightRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightRaw rightStrengthens
  exact Term.idCode_HEq_congr outerLevel levelLe typeCodeRenames
    leftRenames rightRenames

/-- Soundness for equivalence type-code strengthening. -/
theorem partialStrengthenTypedEquivCode_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (targetLeftTypeCodeRaw targetRightTypeCodeRaw : RawTerm targetScope)
    (leftStrengthens :
      leftTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetLeftTypeCodeRaw)
    (rightStrengthens :
      rightTypeCodeRaw.partialStrengthen? strengthening.back =
        some targetRightTypeCodeRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivCode (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw
        targetLeftTypeCodeRaw targetRightTypeCodeRaw
        leftStrengthens rightStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEquivCode,
    StrengtheningResult.renamedTarget]
  have leftRenames :
      leftTypeCodeRaw =
        targetLeftTypeCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftTypeCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftTypeCodeRaw leftStrengthens
  have rightRenames :
      rightTypeCodeRaw =
        targetRightTypeCodeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightTypeCodeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightTypeCodeRaw rightStrengthens
  exact Term.equivCode_HEq_congr outerLevel levelLe leftRenames rightRenames

/-- Soundness for identity reflexivity strengthening. -/
theorem partialStrengthenTypedRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningSoundness
      (partialStrengthenTypedRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        carrierStrengthens witnessStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedRefl, StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have witnessRenames :
      rawWitness = targetWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rawWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetWitness witnessStrengthens
  exact Term.refl_HEq_congr carrierRenames witnessRenames

/-- Soundness for observational-equality reflexivity strengthening. -/
theorem partialStrengthenTypedOeqRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        carrierStrengthens witnessStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOeqRefl, StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have witnessRenames :
      rawWitness = targetWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rawWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetWitness witnessStrengthens
  exact Term.oeqRefl_HEq_congr carrierRenames witnessRenames

/-- Soundness for strict-identity reflexivity strengthening. -/
theorem partialStrengthenTypedIdStrictRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {rawWitness : RawTerm sourceScope}
    {targetWitness : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (witnessStrengthens :
      rawWitness.partialStrengthen? strengthening.back =
        some targetWitness) :
    StrengtheningSoundness
      (partialStrengthenTypedIdStrictRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        modeIsStrict carrierStrengthens witnessStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedIdStrictRefl,
    StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have witnessRenames :
      rawWitness = targetWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rawWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetWitness witnessStrengthens
  exact Term.idStrictRefl_HEq_congr modeIsStrict carrierRenames
    witnessRenames

/-- Soundness for canonical identity equivalence reflexivity
strengthening. -/
theorem partialStrengthenTypedEquivReflId_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivReflId (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        carrier targetCarrier carrierStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEquivReflId,
    StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  exact Term.equivReflId_HEq_congr carrierRenames

/-- Soundness for Id-typed canonical-identity equivalence
strengthening. -/
theorem partialStrengthenTypedEquivReflIdAtId_sound
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (targetCarrier : Ty level targetScope)
    (carrierRaw : RawTerm sourceScope)
    (targetCarrierRaw : RawTerm targetScope)
    (carrierStrengthens :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (carrierRawStrengthens :
      carrierRaw.partialStrengthen? strengthening.back =
        some targetCarrierRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivReflIdAtId (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        innerLevel innerLevelLt carrier targetCarrier
        carrierRaw targetCarrierRaw
        carrierStrengthens carrierRawStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedEquivReflIdAtId,
    StrengtheningResult.renamedTarget]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier strengthening.forward
      strengthening.back strengthening.injectsBack targetCarrier
      carrierStrengthens
  have carrierRawRenames :
      carrierRaw = targetCarrierRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename carrierRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierRaw carrierRawStrengthens
  exact Term.equivReflIdAtId_HEq_congr carrierRenames carrierRawRenames

/-- Soundness for canonical funext reflexivity strengthening. -/
theorem partialStrengthenTypedFunextRefl_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedFunextRefl (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        domainType codomainType targetDomainType targetCodomainType
        applyRaw targetApplyRaw
        domainStrengthens codomainStrengthens applyStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedFunextRefl,
    StrengtheningResult.renamedTarget]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType strengthening.forward
      strengthening.back strengthening.injectsBack targetDomainType
      domainStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType strengthening.forward
      strengthening.back strengthening.injectsBack targetCodomainType
      codomainStrengthens
  have applyRenames :
      applyRaw = targetApplyRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyRaw applyStrengthens
  have congrHEq :
      HEq (Term.funextRefl (context := sourceCtx) domainType codomainType
            applyRaw)
        (Term.funextRefl (context := sourceCtx)
          (targetDomainType.rename strengthening.forward)
          (targetCodomainType.rename strengthening.forward)
          (targetApplyRaw.rename strengthening.forward.lift)) :=
    Term.funextRefl_HEq_congr domainRenames codomainRenames applyRenames
  have castHEq :
      HEq
        (Term.funextRefl (context := sourceCtx)
          (targetDomainType.rename strengthening.forward)
          (targetCodomainType.rename strengthening.forward)
          (targetApplyRaw.rename strengthening.forward.lift))
        ((funextReflType_rename strengthening.forward targetDomainType
            targetCodomainType targetApplyRaw).symm ▸
          Term.funextRefl (context := sourceCtx)
            (targetDomainType.rename strengthening.forward)
            (targetCodomainType.rename strengthening.forward)
            (targetApplyRaw.rename strengthening.forward.lift)) :=
    heq_cast_left
      (motive := fun resultType =>
        Term sourceCtx resultType
          (RawTerm.lam
            (RawTerm.refl
              (targetApplyRaw.rename strengthening.forward.lift))))
      (funextReflType_rename strengthening.forward targetDomainType
        targetCodomainType targetApplyRaw).symm
      (Term.funextRefl (context := sourceCtx)
        (targetDomainType.rename strengthening.forward)
        (targetCodomainType.rename strengthening.forward)
        (targetApplyRaw.rename strengthening.forward.lift))
  exact HEq.trans congrHEq castHEq

/-- Soundness for Id-typed funext reflexivity strengthening. -/
theorem partialStrengthenTypedFunextReflAtId_sound
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (targetApplyRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyStrengthens :
      applyRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedFunextReflAtId (sourceCtx := sourceCtx)
        (targetCtx := targetCtx) (strengthening := strengthening)
        domainType codomainType targetDomainType targetCodomainType
        applyRaw targetApplyRaw
        domainStrengthens codomainStrengthens applyStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedFunextReflAtId,
    StrengtheningResult.renamedTarget]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType strengthening.forward
      strengthening.back strengthening.injectsBack targetDomainType
      domainStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType strengthening.forward
      strengthening.back strengthening.injectsBack targetCodomainType
      codomainStrengthens
  have applyRenames :
      applyRaw = targetApplyRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyRaw applyStrengthens
  exact Term.funextReflAtId_HEq_congr domainRenames codomainRenames
    applyRenames

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

/-- Soundness for refinement-introduction strengthening.  The proof
component lives at `Ty.unit`, which strengthens definitionally; the
predicate carrier and base value contribute the load-bearing renames. -/
theorem partialStrengthenTypedRefineIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetPredicate : RawTerm (targetScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (predicateStrengthens :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    {baseResult : StrengtheningResult strengthening baseValue}
    {proofResult : StrengtheningResult strengthening predicateProof}
    (baseSound : StrengtheningSoundness baseResult)
    (proofSound : StrengtheningSoundness proofResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRefineIntro predicateStrengthens baseResult
        proofResult) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm proofTypeStrengthens
      proofRawStrengthens proofTypeRenames proofRawRenames =>
      cases proofTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedRefineIntro,
          StrengtheningResult.renamedTarget] at proofSound ⊢
      have predicateRenames :
          predicate = targetPredicate.rename strengthening.forward.lift :=
        RawTerm.partialStrengthen?_imp_rename predicate
          strengthening.forward.lift strengthening.back.lift
          (PartialRawRenaming.lift_renamingInjectsBack
            strengthening.injectsBack)
          targetPredicate predicateStrengthens
      exact Term.refineIntro_HEq_congr baseResult.typeRenames predicateRenames
        baseResult.rawRenames proofRawRenames
        baseSound.termRenames proofSound.termRenames

/-- Soundness for the success branch of refinement-elimination
strengthening.  Mirrors `partialStrengthenTypedListElimOfSuccess_sound`:
the term-mode OfSuccess body's record construction is what `dsimp`
unfolds, while the tactic-mode wrapper traversing `Option.casesOn` on
the base/predicate pivots is left unsounded by design. -/
theorem partialStrengthenTypedRefineElimOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {targetRefinedRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    {targetRefinedTerm :
      Term targetCtx (Ty.refine targetBaseType targetPredicate)
        targetRefinedRaw}
    {baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType}
    {predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate}
    {refinedRawStrengthens :
      refinedRaw.partialStrengthen? strengthening.back =
        some targetRefinedRaw}
    {refinedRawRenames :
      refinedRaw = targetRefinedRaw.rename strengthening.forward}
    (refinedSound :
      HEq refinedValue
        (Term.rename strengthening.toTermRenaming targetRefinedTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedRefineElimOfSuccess
        (refinedValue := refinedValue)
        targetRefinedTerm baseSuccess predicateSuccess refinedRawStrengthens
        refinedRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedRefineElimOfSuccess]
  have baseRenames :
      baseType = targetBaseType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  have predicateRenames :
      predicate = targetPredicate.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename predicate
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetPredicate predicateSuccess
  exact Term.refineElim_HEq_congr baseRenames predicateRenames
    refinedRawRenames refinedSound

/-- Soundness for the typed refinement-elimination wrapper.

Mirrors `partialStrengthenTypedRefineElim`'s App-pattern shape: the
wrapper takes `baseSuccess` and `predicateSuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
base type and predicate respectively).  The proof destructures the
refined value's `StrengtheningResult`, aligns the `Ty.refine` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedRefineElimOfSuccess_sound`.  Bypasses Lean
4.29.1 tactic-mode opacity on the original ListElim-pattern wrapper
with two internal option-splits. -/
theorem partialStrengthenTypedRefineElim_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {targetBaseType : Ty level targetScope}
    {targetPredicate : RawTerm (targetScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (predicateSuccess :
      predicate.partialStrengthen? strengthening.back.lift =
        some targetPredicate)
    {refinedResult : StrengtheningResult strengthening refinedValue}
    (refinedSound : StrengtheningSoundness refinedResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRefineElim baseSuccess predicateSuccess
        refinedResult) := by
  cases refinedResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have expectedRefineTypeStrengthens :
          (Ty.refine baseType predicate).partialStrengthen?
              strengthening.back =
            some (Ty.refine targetBaseType targetPredicate) := by
        change
          Option.mapTwo
            (baseType.partialStrengthen? strengthening.back)
            (predicate.partialStrengthen? strengthening.back.lift)
            Ty.refine =
              some (Ty.refine targetBaseType targetPredicate)
        rw [baseSuccess, predicateSuccess]
        rfl
      rw [expectedRefineTypeStrengthens] at typeStrengthens
      cases typeStrengthens
      exact partialStrengthenTypedRefineElimOfSuccess_sound
        (baseSuccess := baseSuccess)
        (predicateSuccess := predicateSuccess)
        (refinedRawStrengthens := rawStrengthens)
        (refinedRawRenames := rawRenames)
        refinedSound.termRenames

/-- Soundness for record-introduction strengthening.  The producer
threads `fieldResult`'s field projections through without destructuring,
so the soundness proof can apply the HEq congruence lemma directly using
the field projections of the result. -/
theorem partialStrengthenTypedRecordIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    {fieldResult : StrengtheningResult strengthening firstField}
    (fieldSound : StrengtheningSoundness fieldResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRecordIntro fieldResult) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedRecordIntro,
      StrengtheningResult.renamedTarget] at fieldSound ⊢
  exact Term.recordIntro_HEq_congr fieldResult.typeRenames
    fieldResult.rawRenames fieldSound.termRenames

/-- Soundness for the success branch of record-projection strengthening.
Mirrors `partialStrengthenTypedRefineElimOfSuccess_sound`: the term-mode
OfSuccess body is what `dsimp` unfolds, while the tactic-mode wrapper
traversing `Option.casesOn` on the field-type pivot is left unsounded
by design. -/
theorem partialStrengthenTypedRecordProjOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {targetFieldType : Ty level targetScope}
    {targetRecordRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    {targetRecordTerm :
      Term targetCtx (Ty.record targetFieldType) targetRecordRaw}
    {fieldSuccess :
      singleFieldType.partialStrengthen? strengthening.back =
        some targetFieldType}
    {recordRawStrengthens :
      recordRaw.partialStrengthen? strengthening.back =
        some targetRecordRaw}
    {recordRawRenames :
      recordRaw = targetRecordRaw.rename strengthening.forward}
    (recordSound :
      HEq recordValue
        (Term.rename strengthening.toTermRenaming targetRecordTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedRecordProjOfSuccess
        (recordValue := recordValue)
        targetRecordTerm fieldSuccess recordRawStrengthens
        recordRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedRecordProjOfSuccess]
  have fieldRenames :
      singleFieldType = targetFieldType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename singleFieldType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetFieldType fieldSuccess
  exact Term.recordProj_HEq_congr fieldRenames recordRawRenames recordSound

/-- Soundness for the typed record-projection wrapper.

Mirrors `partialStrengthenTypedRecordProj`'s structure after the
App-pattern refactor: the wrapper takes the field-type strengthening
witness `fieldSuccess` as an explicit parameter (lifted from the
dispatcher's option-split), destructures the record's
`StrengtheningResult`, aligns the `Ty.record` shape via `rw` + `cases`
on the derived equation, and delegates to
`partialStrengthenTypedRecordProjOfSuccess`.  Soundness threads
`recordSound.termRenames` through the same case cascade and invokes
the leaf `_OfSuccess_sound`. -/
theorem partialStrengthenTypedRecordProj_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {targetFieldType : Ty level targetScope}
    {recordRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (fieldSuccess :
      singleFieldType.partialStrengthen? strengthening.back =
        some targetFieldType)
    {recordResult : StrengtheningResult strengthening recordValue}
    (recordSound : StrengtheningSoundness recordResult) :
    StrengtheningSoundness
      (partialStrengthenTypedRecordProj fieldSuccess recordResult) := by
  cases recordResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      have expectedRecordTypeStrengthens :
          (Ty.record singleFieldType).partialStrengthen? strengthening.back =
            some (Ty.record targetFieldType) := by
        change
          (match singleFieldType.partialStrengthen? strengthening.back with
          | some strengthenedField => some (Ty.record strengthenedField)
          | none => none) =
            some (Ty.record targetFieldType)
        rw [fieldSuccess]
      rw [expectedRecordTypeStrengthens] at typeStrengthens
      cases typeStrengthens
      exact partialStrengthenTypedRecordProjOfSuccess_sound
        (fieldSuccess := fieldSuccess)
        (recordRawStrengthens := rawStrengthens)
        (recordRawRenames := rawRenames)
        recordSound.termRenames

/-- Soundness for the success branch of codata-unfold strengthening.
Mirrors `partialStrengthenTypedAppOfSuccess_sound`: takes pre-decomposed
state/output strengthenings and rename equations, applies the codata-
unfold HEq congruence lemma after deriving the state/output type
renames from the strengthening's injectivity. -/
theorem partialStrengthenTypedCodataUnfoldOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {targetStateRaw targetTransitionRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    {targetStateTerm : Term targetCtx targetStateType targetStateRaw}
    {targetTransitionTerm :
      Term targetCtx (Ty.arrow targetStateType targetOutputType)
        targetTransitionRaw}
    {stateTypeStrengthens :
      stateType.partialStrengthen? strengthening.back = some targetStateType}
    {outputTypeStrengthens :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType}
    {stateRawStrengthens :
      stateRaw.partialStrengthen? strengthening.back =
        some targetStateRaw}
    {transitionRawStrengthens :
      transitionRaw.partialStrengthen? strengthening.back =
        some targetTransitionRaw}
    {stateRawRenames :
      stateRaw = targetStateRaw.rename strengthening.forward}
    {transitionRawRenames :
      transitionRaw = targetTransitionRaw.rename strengthening.forward}
    (stateSound :
      HEq initialState
        (Term.rename strengthening.toTermRenaming targetStateTerm))
    (transitionSound :
      HEq transition
        (Term.rename strengthening.toTermRenaming targetTransitionTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataUnfoldOfSuccess
        (initialState := initialState) (transition := transition)
        targetStateTerm targetTransitionTerm stateTypeStrengthens
        outputTypeStrengthens stateRawStrengthens transitionRawStrengthens
        stateRawRenames transitionRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedCodataUnfoldOfSuccess]
  have stateRenames :
      stateType = targetStateType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename stateType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetStateType stateTypeStrengthens
  have outputRenames :
      outputType = targetOutputType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename outputType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetOutputType outputTypeStrengthens
  exact Term.codataUnfold_HEq_congr stateRenames outputRenames
    stateRawRenames transitionRawRenames stateSound transitionSound

/-- Soundness for the typed codata-unfold wrapper.

Mirrors `partialStrengthenTypedCodataUnfold`'s structure: destructures
both child `StrengtheningResult` records, aligns the transition's
`Ty.arrow` type via `rw` + `cases` on the transition-type
strengthening, then invokes
`partialStrengthenTypedCodataUnfoldOfSuccess_sound` at the leaf with
the explicit `outputTypeStrengthens` witness threaded through.  Pure
App-pattern: no internal `cases X : foo` option-split, only record
field rewrites. -/
theorem partialStrengthenTypedCodataUnfold_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetOutputType : Ty level targetScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (outputTypeStrengthens :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    {stateResult : StrengtheningResult strengthening initialState}
    {transitionResult : StrengtheningResult strengthening transition}
    (stateSound : StrengtheningSoundness stateResult)
    (transitionSound : StrengtheningSoundness transitionResult) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataUnfold outputTypeStrengthens
        stateResult transitionResult) := by
  cases stateResult with
  | mk targetStateType targetStateRaw targetStateTerm stateTypeStrengthens
      stateRawStrengthens stateTypeRenames stateRawRenames =>
      cases transitionResult with
      | mk targetTransitionType targetTransitionRaw targetTransitionTerm
          transitionTypeStrengthens transitionRawStrengthens
          transitionTypeRenames transitionRawRenames =>
          have expectedTransitionTypeStrengthens :
              (Ty.arrow stateType outputType).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetStateType targetOutputType) := by
            change
              Option.mapTwo
                (stateType.partialStrengthen? strengthening.back)
                (outputType.partialStrengthen? strengthening.back)
                Ty.arrow =
                  some (Ty.arrow targetStateType targetOutputType)
            rw [stateTypeStrengthens, outputTypeStrengthens]
            rfl
          rw [expectedTransitionTypeStrengthens]
            at transitionTypeStrengthens
          cases transitionTypeStrengthens
          exact partialStrengthenTypedCodataUnfoldOfSuccess_sound
            (stateTypeStrengthens := stateTypeStrengthens)
            (outputTypeStrengthens := outputTypeStrengthens)
            (stateRawStrengthens := stateRawStrengthens)
            (transitionRawStrengthens := transitionRawStrengthens)
            (stateRawRenames := stateRawRenames)
            (transitionRawRenames := transitionRawRenames)
            stateSound.termRenames transitionSound.termRenames

/-- Soundness for the success branch of codata-destruction strengthening.
Mirrors `partialStrengthenTypedRefineElimOfSuccess_sound`: the OfSuccess
body's record construction is what `dsimp` unfolds.  The state-type
strengthening witness is unused by the produced output type but stays
in the signature for symmetry with the wrapper's case cascade. -/
theorem partialStrengthenTypedCodataDestOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {codataRaw : RawTerm sourceScope}
    {targetCodataRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    {targetCodataTerm :
      Term targetCtx (Ty.codata targetStateType targetOutputType)
        targetCodataRaw}
    {stateSuccess :
      stateType.partialStrengthen? strengthening.back = some targetStateType}
    {outputSuccess :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType}
    {codataRawStrengthens :
      codataRaw.partialStrengthen? strengthening.back =
        some targetCodataRaw}
    {codataRawRenames :
      codataRaw = targetCodataRaw.rename strengthening.forward}
    (codataSound :
      HEq codataValue
        (Term.rename strengthening.toTermRenaming targetCodataTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataDestOfSuccess
        (codataValue := codataValue)
        targetCodataTerm stateSuccess outputSuccess codataRawStrengthens
        codataRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedCodataDestOfSuccess]
  have stateRenames :
      stateType = targetStateType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename stateType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetStateType stateSuccess
  have outputRenames :
      outputType = targetOutputType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename outputType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetOutputType outputSuccess
  exact Term.codataDest_HEq_congr stateRenames outputRenames
    codataRawRenames codataSound

/-- Soundness for the typed codata-destruction wrapper.

Mirrors `partialStrengthenTypedCodataDest`'s App-pattern shape: the
wrapper takes `stateSuccess` and `outputSuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
state and output type respectively).  The proof destructures the
codata value's `StrengtheningResult`, aligns the `Ty.codata` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedCodataDestOfSuccess_sound`.  Same recipe as
Phase 39 RefineElim. -/
theorem partialStrengthenTypedCodataDest_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {targetStateType targetOutputType : Ty level targetScope}
    {codataRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (stateSuccess :
      stateType.partialStrengthen? strengthening.back = some targetStateType)
    (outputSuccess :
      outputType.partialStrengthen? strengthening.back =
        some targetOutputType)
    {codataResult : StrengtheningResult strengthening codataValue}
    (codataSound : StrengtheningSoundness codataResult) :
    StrengtheningSoundness
      (partialStrengthenTypedCodataDest stateSuccess outputSuccess
        codataResult) := by
  cases codataResult with
  | mk targetCodataType targetCodataRaw targetCodataTerm
      codataTypeStrengthens codataRawStrengthens codataTypeRenames
      codataRawRenames =>
      have expectedCodataTypeStrengthens :
          (Ty.codata stateType outputType).partialStrengthen?
              strengthening.back =
            some (Ty.codata targetStateType targetOutputType) := by
        change
          Option.mapTwo
            (stateType.partialStrengthen? strengthening.back)
            (outputType.partialStrengthen? strengthening.back)
            Ty.codata =
              some (Ty.codata targetStateType targetOutputType)
        rw [stateSuccess, outputSuccess]
        rfl
      rw [expectedCodataTypeStrengthens] at codataTypeStrengthens
      cases codataTypeStrengthens
      exact partialStrengthenTypedCodataDestOfSuccess_sound
        (stateSuccess := stateSuccess)
        (outputSuccess := outputSuccess)
        (codataRawStrengthens := codataRawStrengthens)
        (codataRawRenames := codataRawRenames)
        codataSound.termRenames

/-- Soundness for session-send strengthening.  The producer is direct
(no Option.casesOn discriminator wall — protocol pivot is pre-witnessed
by the `protocolStrengthens` hypothesis), so soundness mirrors the
producer's case structure with the same `change / rw / cases` chain
to unify the channel's session type with the target's protocol step. -/
theorem partialStrengthenTypedSessionSend_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {targetProtocolStep : RawTerm targetScope}
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (protocolStrengthens :
      protocolStep.partialStrengthen? strengthening.back =
        some targetProtocolStep)
    {channelResult : StrengtheningResult strengthening channel}
    {payloadResult : StrengtheningResult strengthening payload}
    (channelSound : StrengtheningSoundness channelResult)
    (payloadSound : StrengtheningSoundness payloadResult) :
    StrengtheningSoundness
      (partialStrengthenTypedSessionSend protocolStrengthens channelResult
        payloadResult) := by
  cases channelResult with
  | mk targetChannelType targetChannelRaw targetChannelTerm
      channelTypeStrengthens channelRawStrengthens channelTypeRenames
      channelRawRenames =>
      change
        (match protocolStep.partialStrengthen? strengthening.back with
        | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
        | none => none) = some targetChannelType at channelTypeStrengthens
      rw [protocolStrengthens] at channelTypeStrengthens
      cases channelTypeStrengthens
      cases payloadResult with
      | mk targetPayloadType targetPayloadRaw targetPayloadTerm
          payloadTypeStrengthens payloadRawStrengthens payloadTypeRenames
          payloadRawRenames =>
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedSessionSend,
              StrengtheningResult.renamedTarget] at channelSound payloadSound ⊢
          have protocolRenames :
              protocolStep = targetProtocolStep.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename protocolStep
              strengthening.forward strengthening.back strengthening.injectsBack
              targetProtocolStep protocolStrengthens
          exact Term.sessionSend_HEq_congr protocolRenames
            payloadTypeRenames channelRawRenames payloadRawRenames
            channelSound.termRenames payloadSound.termRenames

/-- Soundness for session-receive strengthening.  Mirrors the session-send
soundness pattern with one fewer payload component: the producer cases the
channel result and unifies the session type via `change / rw / cases` on
the channel's typeStrengthens witness. -/
theorem partialStrengthenTypedSessionRecv_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {targetProtocolStep : RawTerm targetScope}
    {channelRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (protocolStrengthens :
      protocolStep.partialStrengthen? strengthening.back =
        some targetProtocolStep)
    {channelResult : StrengtheningResult strengthening channel}
    (channelSound : StrengtheningSoundness channelResult) :
    StrengtheningSoundness
      (partialStrengthenTypedSessionRecv protocolStrengthens
        channelResult) := by
  cases channelResult with
  | mk targetChannelType targetChannelRaw targetChannelTerm
      channelTypeStrengthens channelRawStrengthens channelTypeRenames
      channelRawRenames =>
      change
        (match protocolStep.partialStrengthen? strengthening.back with
        | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
        | none => none) = some targetChannelType at channelTypeStrengthens
      rw [protocolStrengthens] at channelTypeStrengthens
      cases channelTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedSessionRecv,
          StrengtheningResult.renamedTarget] at channelSound ⊢
      have protocolRenames :
          protocolStep = targetProtocolStep.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename protocolStep
          strengthening.forward strengthening.back strengthening.injectsBack
          targetProtocolStep protocolStrengthens
      exact Term.sessionRecv_HEq_congr protocolRenames channelRawRenames
        channelSound.termRenames

/-- Soundness for cumulativity-promotion strengthening.  The producer is
direct: the type-code's source type is `Ty.universe lowerLevel levelLeLow`
(closed in scope), so its partial-strengthen reduces definitionally to
`some (Ty.universe lowerLevel levelLeLow)` and `cases` unifies cleanly.
Only the code's raw rename equation is load-bearing. -/
theorem partialStrengthenTypedCumulUp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    {codeResult : StrengtheningResult strengthening typeCode}
    (codeSound : StrengtheningSoundness codeResult) :
    StrengtheningSoundness
      (partialStrengthenTypedCumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh codeResult) := by
  cases codeResult with
  | mk targetCodeType targetCodeRaw targetCodeTerm codeTypeStrengthens
      codeRawStrengthens codeTypeRenames codeRawRenames =>
      cases codeTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedCumulUp,
          StrengtheningResult.renamedTarget] at codeSound ⊢
      exact Term.cumulUp_HEq_congr codeRawRenames codeSound.termRenames

/-- Soundness for univalence-β extraction.  The producer is direct: all
four type/raw pivots (`leftTy`, `rightTy`, `leftTyRaw`, `rightTyRaw`) are
pre-witnessed by hypotheses, and the proof's typeStrengthens is unified
via a synthesized `expectedProofTypeStrengthens` rewrite to discharge
the `Ty.id (Ty.universe ...)` shape.  Mirrors the producer's case chain
so the HEq congruence applies directly. -/
theorem partialStrengthenTypedUaToEquiv_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (targetLeftTy targetRightTy : Ty level targetScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    (targetLeftTyRaw targetRightTyRaw : RawTerm targetScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw}
    (leftTyStrengthens :
      leftTy.partialStrengthen? strengthening.back = some targetLeftTy)
    (rightTyStrengthens :
      rightTy.partialStrengthen? strengthening.back = some targetRightTy)
    (leftRawStrengthens :
      leftTyRaw.partialStrengthen? strengthening.back = some targetLeftTyRaw)
    (rightRawStrengthens :
      rightTyRaw.partialStrengthen? strengthening.back = some targetRightTyRaw)
    {proofResult : StrengtheningResult strengthening proof}
    (proofSound : StrengtheningSoundness proofResult) :
    StrengtheningSoundness
      (partialStrengthenTypedUaToEquiv innerLevel innerLevelLt leftTy
        rightTy targetLeftTy targetRightTy leftTyRaw rightTyRaw
        targetLeftTyRaw targetRightTyRaw leftTyStrengthens rightTyStrengthens
        leftRawStrengthens rightRawStrengthens proofResult) := by
  cases proofResult with
  | mk targetProofType targetProofRaw targetProofTerm
      proofTypeStrengthens proofRawStrengthens proofTypeRenames
      proofRawRenames =>
      have expectedProofTypeStrengthens :
          (Ty.id (Ty.universe innerLevel innerLevelLt)
              leftTyRaw rightTyRaw).partialStrengthen? strengthening.back =
            some (Ty.id (Ty.universe innerLevel innerLevelLt)
              targetLeftTyRaw targetRightTyRaw) := by
        change
          Option.mapThree
            ((Ty.universe innerLevel innerLevelLt).partialStrengthen?
              strengthening.back)
            (leftTyRaw.partialStrengthen? strengthening.back)
            (rightTyRaw.partialStrengthen? strengthening.back)
            Ty.id =
              some (Ty.id (Ty.universe innerLevel innerLevelLt)
                targetLeftTyRaw targetRightTyRaw)
        rw [leftRawStrengthens, rightRawStrengthens]
        rfl
      rw [expectedProofTypeStrengthens] at proofTypeStrengthens
      cases proofTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedUaToEquiv,
          StrengtheningResult.renamedTarget] at proofSound ⊢
      have leftTyRenames :
          leftTy = targetLeftTy.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename leftTy
          strengthening.forward strengthening.back strengthening.injectsBack
          targetLeftTy leftTyStrengthens
      have rightTyRenames :
          rightTy = targetRightTy.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename rightTy
          strengthening.forward strengthening.back strengthening.injectsBack
          targetRightTy rightTyStrengthens
      have leftRawRenames :
          leftTyRaw = targetLeftTyRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename leftTyRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetLeftTyRaw leftRawStrengthens
      have rightRawRenames :
          rightTyRaw = targetRightTyRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename rightTyRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetRightTyRaw rightRawStrengthens
      exact Term.uaToEquiv_HEq_congr leftTyRenames rightTyRenames
        leftRawRenames rightRawRenames proofRawRenames
        proofSound.termRenames

/-- Soundness for heterogeneous funext introduction.  The producer has
no Term children — the strengthened result is built purely from
strengthening witnesses on the four type/raw pivots.  Soundness derives
all four renames via `partialStrengthen?_imp_rename` and applies the HEq
congruence directly. -/
theorem partialStrengthenTypedFunextIntroHet_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1))
    (targetApplyARaw targetApplyBRaw : RawTerm (targetScope + 1))
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (applyAStrengthens :
      applyARaw.partialStrengthen? strengthening.back.lift =
        some targetApplyARaw)
    (applyBStrengthens :
      applyBRaw.partialStrengthen? strengthening.back.lift =
        some targetApplyBRaw) :
    StrengtheningSoundness
      (partialStrengthenTypedFunextIntroHet domainType codomainType
        targetDomainType targetCodomainType applyARaw applyBRaw
        targetApplyARaw targetApplyBRaw domainStrengthens codomainStrengthens
        applyAStrengthens applyBStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedFunextIntroHet,
      StrengtheningResult.renamedTarget]
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCodomainType codomainStrengthens
  have applyARenames :
      applyARaw = targetApplyARaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyARaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyARaw applyAStrengthens
  have applyBRenames :
      applyBRaw = targetApplyBRaw.rename strengthening.forward.lift :=
    RawTerm.partialStrengthen?_imp_rename applyBRaw
      strengthening.forward.lift strengthening.back.lift
      (PartialRawRenaming.lift_renamingInjectsBack
        strengthening.injectsBack)
      targetApplyBRaw applyBStrengthens
  exact Term.funextIntroHet_HEq_congr domainRenames codomainRenames
    applyARenames applyBRenames

/-- Soundness for heterogeneous univalence introduction.  Mirrors the
producer's case chain: cases equivResult, build the expected
`Ty.equiv` and `RawTerm.equivIntro` strengthenings via the six pre-
witnesses, rw + cases to unify the equiv type and raw, then apply
`uaIntroHet_HEq_congr` with the derived renames. -/
theorem partialStrengthenTypedUaIntroHet_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (targetCarrierA targetCarrierB : Ty level targetScope)
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    (targetCarrierARaw targetCarrierBRaw : RawTerm targetScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (targetForwardRaw targetBackwardRaw : RawTerm targetScope)
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (carrierAStrengthens :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBStrengthens :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (carrierARawStrengthens :
      carrierARaw.partialStrengthen? strengthening.back =
        some targetCarrierARaw)
    (carrierBRawStrengthens :
      carrierBRaw.partialStrengthen? strengthening.back =
        some targetCarrierBRaw)
    (forwardRawStrengthens :
      forwardRaw.partialStrengthen? strengthening.back =
        some targetForwardRaw)
    (backwardRawStrengthens :
      backwardRaw.partialStrengthen? strengthening.back =
        some targetBackwardRaw)
    {equivResult : StrengtheningResult strengthening equivWitness}
    (equivSound : StrengtheningSoundness equivResult) :
    StrengtheningSoundness
      (partialStrengthenTypedUaIntroHet innerLevel innerLevelLt
        targetCarrierA targetCarrierB carrierARaw carrierBRaw
        targetCarrierARaw targetCarrierBRaw targetForwardRaw targetBackwardRaw
        carrierAStrengthens carrierBStrengthens carrierARawStrengthens
        carrierBRawStrengthens forwardRawStrengthens backwardRawStrengthens
        equivResult) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivWitness
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv =
              some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierAStrengthens, carrierBStrengthens]
        rfl
      have expectedEquivRawStrengthens :
          (RawTerm.equivIntro forwardRaw backwardRaw).partialStrengthen?
              strengthening.back =
            some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw) := by
        change
          Option.mapTwo
            (forwardRaw.partialStrengthen? strengthening.back)
            (backwardRaw.partialStrengthen? strengthening.back)
            RawTerm.equivIntro =
              some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw)
        rw [forwardRawStrengthens, backwardRawStrengthens]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      rw [expectedEquivRawStrengthens] at equivRawStrengthens
      cases equivTypeStrengthens
      cases equivRawStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedUaIntroHet,
          StrengtheningResult.renamedTarget] at equivSound ⊢
      have carrierARenames :
          carrierA = targetCarrierA.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename carrierA
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierA carrierAStrengthens
      have carrierBRenames :
          carrierB = targetCarrierB.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename carrierB
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierB carrierBStrengthens
      have carrierARawRenames :
          carrierARaw = targetCarrierARaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename carrierARaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierARaw carrierARawStrengthens
      have carrierBRawRenames :
          carrierBRaw = targetCarrierBRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename carrierBRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCarrierBRaw carrierBRawStrengthens
      have forwardRawRenames :
          forwardRaw = targetForwardRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename forwardRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetForwardRaw forwardRawStrengthens
      have backwardRawRenames :
          backwardRaw = targetBackwardRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename backwardRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetBackwardRaw backwardRawStrengthens
      exact Term.uaIntroHet_HEq_congr innerLevel innerLevelLt
        carrierARenames carrierBRenames carrierARawRenames carrierBRawRenames
        forwardRawRenames backwardRawRenames equivSound.termRenames

/-- Soundness for cubical Glue introduction.  Direct producer: both
sub-Term children share the same `baseType` (pre-witnessed by
`baseTypeStrengthens`).  Mirrors the producer's two-cases chain
(`cases baseResult; rw + cases; cases partialResult; rw + cases`) and
applies `glueIntro_HEq_congr` with the two pre-witnessed renames plus
the sub-Terms' soundness HEqs. -/
theorem partialStrengthenTypedGlueIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (targetBaseType : Ty level targetScope)
    (boundaryWitness : RawTerm sourceScope)
    (targetBoundaryWitness : RawTerm targetScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseTypeStrengthens :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundaryStrengthens :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    {baseResult : StrengtheningResult strengthening baseValue}
    {partialResult : StrengtheningResult strengthening partialValue}
    (baseSound : StrengtheningSoundness baseResult)
    (partialSound : StrengtheningSoundness partialResult) :
    StrengtheningSoundness
      (partialStrengthenTypedGlueIntro modeIsUnivalent baseType
        targetBaseType boundaryWitness targetBoundaryWitness
        baseTypeStrengthens boundaryStrengthens baseResult partialResult) := by
  cases baseResult with
  | mk targetBaseValueType targetBaseRaw targetBaseValue
      baseValueTypeStrengthens baseRawStrengthens baseValueTypeRenames
      baseRawRenames =>
      rw [baseTypeStrengthens] at baseValueTypeStrengthens
      cases baseValueTypeStrengthens
      cases partialResult with
      | mk targetPartialValueType targetPartialRaw targetPartialValue
          partialValueTypeStrengthens partialRawStrengthens
          partialValueTypeRenames partialRawRenames =>
          rw [baseTypeStrengthens] at partialValueTypeStrengthens
          cases partialValueTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedGlueIntro,
              StrengtheningResult.renamedTarget]
            at baseSound partialSound ⊢
          have baseRenames :
              baseType = targetBaseType.rename strengthening.forward :=
            Ty.partialStrengthen?_imp_rename baseType
              strengthening.forward strengthening.back
              strengthening.injectsBack targetBaseType baseTypeStrengthens
          have boundaryRenames :
              boundaryWitness =
                targetBoundaryWitness.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename boundaryWitness
              strengthening.forward strengthening.back
              strengthening.injectsBack targetBoundaryWitness
              boundaryStrengthens
          exact Term.glueIntro_HEq_congr modeIsUnivalent baseRenames
            boundaryRenames baseRawRenames partialRawRenames
            baseSound.termRenames partialSound.termRenames

/-- Soundness for observational funext.  Bridges the rename-distribution
cast on `oeqFunextPointwiseType` via the published commutation lemma
`oeqFunextPointwiseType_rename`, which `Term.rename` itself uses with an
explicit `▸` cast in the `oeqFunext` arm.  The HEq congruence's
expected `pointwiseProof2` parameter therefore arrives in the cast
shape `typeEq ▸ Term.rename ... targetPointwiseProof`, and we bridge
`pointwiseSound.termRenames` to that shape via
`Term.type_eq_cast_heq` + `HEq.trans` + `HEq.symm`. -/
theorem partialStrengthenTypedOeqFunext_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (domainType codomainType : Ty level sourceScope)
    (targetDomainType targetCodomainType : Ty level targetScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    (targetLeftFunctionRaw targetRightFunctionRaw : RawTerm targetScope)
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (domainStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    (leftFunctionStrengthens :
      leftFunctionRaw.partialStrengthen? strengthening.back =
        some targetLeftFunctionRaw)
    (rightFunctionStrengthens :
      rightFunctionRaw.partialStrengthen? strengthening.back =
        some targetRightFunctionRaw)
    {pointwiseResult : StrengtheningResult strengthening pointwiseProof}
    (pointwiseSound : StrengtheningSoundness pointwiseResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqFunext domainType codomainType
        targetDomainType targetCodomainType leftFunctionRaw rightFunctionRaw
        targetLeftFunctionRaw targetRightFunctionRaw domainStrengthens
        codomainStrengthens leftFunctionStrengthens rightFunctionStrengthens
        pointwiseResult) := by
  cases pointwiseResult with
  | mk targetPointwiseType targetPointwiseRaw targetPointwiseProof
      pointwiseTypeStrengthens pointwiseRawStrengthens
      pointwiseTypeRenames pointwiseRawRenames =>
      have codomainWeakenStrengthens :
          codomainType.weaken.partialStrengthen? strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift codomainType
          strengthening.back, codomainStrengthens]
        rfl
      have leftWeakenStrengthens :
          leftFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetLeftFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift leftFunctionRaw
          strengthening.back, leftFunctionStrengthens]
        rfl
      have rightWeakenStrengthens :
          rightFunctionRaw.weaken.partialStrengthen?
              strengthening.back.lift =
            some targetRightFunctionRaw.weaken := by
        rw [RawTerm.partialStrengthen?_weaken_lift rightFunctionRaw
          strengthening.back, rightFunctionStrengthens]
        rfl
      have pointwiseExpectedStrengthens :
          (oeqFunextPointwiseType domainType codomainType
              leftFunctionRaw rightFunctionRaw).partialStrengthen?
              strengthening.back =
            some (oeqFunextPointwiseType targetDomainType targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw) := by
        have codomainBodyStrengthens :
            (oeqFunextPointwiseCodomain codomainType
                leftFunctionRaw rightFunctionRaw).partialStrengthen?
                strengthening.back.lift =
              some (oeqFunextPointwiseCodomain targetCodomainType
                targetLeftFunctionRaw targetRightFunctionRaw) := by
          have leftAppStrengthens :
              (RawTerm.app leftFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetLeftFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (leftFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetLeftFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [leftWeakenStrengthens]
            rfl
          have rightAppStrengthens :
              (RawTerm.app rightFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetRightFunctionRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (rightFunctionRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetRightFunctionRaw.weaken
                    (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [rightWeakenStrengthens]
            rfl
          change
            Option.mapThree
              (codomainType.weaken.partialStrengthen?
                strengthening.back.lift)
              ((RawTerm.app leftFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift)
              ((RawTerm.app rightFunctionRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift)
              Ty.oeq =
                some (oeqFunextPointwiseCodomain targetCodomainType
                  targetLeftFunctionRaw targetRightFunctionRaw)
          rw [codomainWeakenStrengthens, leftAppStrengthens,
            rightAppStrengthens]
          rfl
        change
          Option.mapTwo
            (domainType.partialStrengthen? strengthening.back)
            ((oeqFunextPointwiseCodomain codomainType
                leftFunctionRaw rightFunctionRaw).partialStrengthen?
                strengthening.back.lift)
            Ty.piTy =
              some (oeqFunextPointwiseType targetDomainType
                targetCodomainType targetLeftFunctionRaw
                targetRightFunctionRaw)
        rw [domainStrengthens, codomainBodyStrengthens]
        rfl
      rw [pointwiseExpectedStrengthens] at pointwiseTypeStrengthens
      cases pointwiseTypeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedOeqFunext,
          StrengtheningResult.renamedTarget] at pointwiseSound ⊢
      have domainRenames :
          domainType = targetDomainType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename domainType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetDomainType domainStrengthens
      have codomainRenames :
          codomainType = targetCodomainType.rename strengthening.forward :=
        Ty.partialStrengthen?_imp_rename codomainType
          strengthening.forward strengthening.back strengthening.injectsBack
          targetCodomainType codomainStrengthens
      have leftFunctionRenames :
          leftFunctionRaw =
            targetLeftFunctionRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename leftFunctionRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetLeftFunctionRaw leftFunctionStrengthens
      have rightFunctionRenames :
          rightFunctionRaw =
            targetRightFunctionRaw.rename strengthening.forward :=
        RawTerm.partialStrengthen?_imp_rename rightFunctionRaw
          strengthening.forward strengthening.back strengthening.injectsBack
          targetRightFunctionRaw rightFunctionStrengthens
      have typeEq :
          (oeqFunextPointwiseType targetDomainType targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw).rename
              strengthening.forward =
            oeqFunextPointwiseType
              (targetDomainType.rename strengthening.forward)
              (targetCodomainType.rename strengthening.forward)
              (targetLeftFunctionRaw.rename strengthening.forward)
              (targetRightFunctionRaw.rename strengthening.forward) :=
        oeqFunextPointwiseType_rename strengthening.forward
          targetDomainType targetCodomainType targetLeftFunctionRaw
          targetRightFunctionRaw
      have castedHEq :
          HEq
            (Term.rename strengthening.toTermRenaming targetPointwiseProof)
            (typeEq ▸
              Term.rename strengthening.toTermRenaming targetPointwiseProof) :=
        HEq.symm
          (Term.type_eq_cast_heq typeEq
            (Term.rename strengthening.toTermRenaming targetPointwiseProof))
      have pointwiseHEq :
          HEq pointwiseProof
            (typeEq ▸
              Term.rename strengthening.toTermRenaming targetPointwiseProof) :=
        HEq.trans pointwiseSound.termRenames castedHEq
      exact Term.oeqFunext_HEq_congr domainRenames codomainRenames
        leftFunctionRenames rightFunctionRenames pointwiseRawRenames
        pointwiseHEq

/-- Soundness for the success branch of identity-elimination
strengthening.  The producer's success-arm record is what `dsimp`
unfolds — the wrapper's `cases` cascade on the witness's `Ty.id`
parameters is left unsounded by design (the OfSuccess pattern from
RefineElim/RecordProj/CodataDest/etc.).  `Ty.id` is a Ty constructor
so `Ty.rename` distributes definitionally, no cast bridge needed. -/
theorem partialStrengthenTypedIdJOfSuccess_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    {targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw}
    {targetWitnessTerm :
      Term targetCtx
        (Ty.id targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw}
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward)
    (baseSound :
      HEq baseCase
        (Term.rename strengthening.toTermRenaming targetBaseTerm))
    (witnessSound :
      HEq witness
        (Term.rename strengthening.toTermRenaming targetWitnessTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedIdJOfSuccess
        (baseCase := baseCase) (witness := witness)
        targetBaseTerm targetWitnessTerm baseTypeStrengthens
        carrierSuccess leftSuccess rightSuccess baseRawStrengthens
        witnessRawStrengthens baseTypeRenames baseRawRenames
        witnessRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedIdJOfSuccess]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierSuccess
  have leftRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightRenames :
      rightEndpoint = targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.idJ_HEq_congr carrierRenames leftRenames rightRenames
    baseTypeRenames baseRawRenames witnessRawRenames baseSound witnessSound

/-- Soundness for the success branch of observational-equality
elimination strengthening.  Mirrors `partialStrengthenTypedIdJOfSuccess_sound`
with `Ty.oeq` in place of `Ty.id`. -/
theorem partialStrengthenTypedOeqJOfSuccess_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    {targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw}
    {targetWitnessTerm :
      Term targetCtx
        (Ty.oeq targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw}
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward)
    (baseSound :
      HEq baseCase
        (Term.rename strengthening.toTermRenaming targetBaseTerm))
    (witnessSound :
      HEq witness
        (Term.rename strengthening.toTermRenaming targetWitnessTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqJOfSuccess
        (baseCase := baseCase) (witness := witness)
        targetBaseTerm targetWitnessTerm baseTypeStrengthens
        carrierSuccess leftSuccess rightSuccess baseRawStrengthens
        witnessRawStrengthens baseTypeRenames baseRawRenames
        witnessRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedOeqJOfSuccess]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierSuccess
  have leftRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightRenames :
      rightEndpoint = targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.oeqJ_HEq_congr carrierRenames leftRenames rightRenames
    baseTypeRenames baseRawRenames witnessRawRenames baseSound witnessSound

/-- Soundness for the success branch of strict-identity-recursor
strengthening.  Mirrors `partialStrengthenTypedIdJOfSuccess_sound`
with `Ty.idStrict` and the `modeIsStrict` evidence. -/
theorem partialStrengthenTypedIdStrictRecOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {targetMotiveType : Ty level targetScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {targetBaseRaw targetWitnessRaw : RawTerm targetScope}
    {targetCarrier : Ty level targetScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    {targetBaseTerm : Term targetCtx targetMotiveType targetBaseRaw}
    {targetWitnessTerm :
      Term targetCtx
        (Ty.idStrict targetCarrier targetLeftEndpoint targetRightEndpoint)
        targetWitnessRaw}
    (baseTypeStrengthens :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (baseRawStrengthens :
      baseRaw.partialStrengthen? strengthening.back = some targetBaseRaw)
    (witnessRawStrengthens :
      witnessRaw.partialStrengthen? strengthening.back =
        some targetWitnessRaw)
    (baseTypeRenames :
      motiveType = targetMotiveType.rename strengthening.forward)
    (baseRawRenames : baseRaw = targetBaseRaw.rename strengthening.forward)
    (witnessRawRenames :
      witnessRaw = targetWitnessRaw.rename strengthening.forward)
    (baseSound :
      HEq baseCase
        (Term.rename strengthening.toTermRenaming targetBaseTerm))
    (witnessSound :
      HEq witness
        (Term.rename strengthening.toTermRenaming targetWitnessTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedIdStrictRecOfSuccess modeIsStrict
        (baseCase := baseCase) (witness := witness)
        targetBaseTerm targetWitnessTerm baseTypeStrengthens
        carrierSuccess leftSuccess rightSuccess baseRawStrengthens
        witnessRawStrengthens baseTypeRenames baseRawRenames
        witnessRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedIdStrictRecOfSuccess]
  have carrierRenames :
      carrier = targetCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrier carrierSuccess
  have leftRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightRenames :
      rightEndpoint = targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.idStrictRec_HEq_congr modeIsStrict carrierRenames leftRenames
    rightRenames baseTypeRenames baseRawRenames witnessRawRenames
    baseSound witnessSound

/-- Soundness for the success branch of equiv-application strengthening.
Direct mirror of `partialStrengthenTypedIdJOfSuccess_sound` with dual
carrier pivots; no cast bridge needed since `Ty.equiv` is a Ty
constructor and `Ty.rename` distributes definitionally. -/
theorem partialStrengthenTypedEquivApplyOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    {targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw}
    {targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward)
    (equivSound :
      HEq equivTerm
        (Term.rename strengthening.toTermRenaming targetEquivTerm))
    (argumentSound :
      HEq argumentTerm
        (Term.rename strengthening.toTermRenaming targetArgumentTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivApplyOfSuccess
        (equivTerm := equivTerm) (argumentTerm := argumentTerm)
        targetEquivTerm targetArgumentTerm carrierASuccess carrierBSuccess
        equivRawStrengthens argumentRawStrengthens equivRawRenames
        argumentRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEquivApplyOfSuccess]
  have carrierARenames :
      carrierA = targetCarrierA.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierA
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierA carrierASuccess
  have carrierBRenames :
      carrierB = targetCarrierB.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  exact Term.equivApply_HEq_congr carrierARenames carrierBRenames
    equivRawRenames argumentRawRenames equivSound argumentSound

/-- Soundness for the success branch of equivalence-application
strengthening.  Mirrors `partialStrengthenTypedEquivApplyOfSuccess_sound`
with `Term.equivApp` / `RawTerm.equivApp` in place of the
univalence-β `equivApply`. -/
theorem partialStrengthenTypedEquivAppOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {targetEquivRaw targetArgumentRaw : RawTerm targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    {targetEquivTerm :
      Term targetCtx (Ty.equiv targetCarrierA targetCarrierB) targetEquivRaw}
    {targetArgumentTerm :
      Term targetCtx targetCarrierA targetArgumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    (equivRawStrengthens :
      equivRaw.partialStrengthen? strengthening.back = some targetEquivRaw)
    (argumentRawStrengthens :
      argumentRaw.partialStrengthen? strengthening.back =
        some targetArgumentRaw)
    (equivRawRenames :
      equivRaw = targetEquivRaw.rename strengthening.forward)
    (argumentRawRenames :
      argumentRaw = targetArgumentRaw.rename strengthening.forward)
    (equivSound :
      HEq equivTerm
        (Term.rename strengthening.toTermRenaming targetEquivTerm))
    (argumentSound :
      HEq argumentTerm
        (Term.rename strengthening.toTermRenaming targetArgumentTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivAppOfSuccess
        (equivTerm := equivTerm) (argumentTerm := argumentTerm)
        targetEquivTerm targetArgumentTerm carrierASuccess carrierBSuccess
        equivRawStrengthens argumentRawStrengthens equivRawRenames
        argumentRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEquivAppOfSuccess]
  have carrierARenames :
      carrierA = targetCarrierA.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierA
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierA carrierASuccess
  have carrierBRenames :
      carrierB = targetCarrierB.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  exact Term.equivApp_HEq_congr carrierARenames carrierBRenames
    equivRawRenames argumentRawRenames equivSound argumentSound

/-- Soundness for dependent lambda strengthening.

The wrapper takes `body : Term (sourceCtx.cons domainType) codomainType
bodyRaw` and produces `Term.lamPi body`.  The renamedTarget is
`Term.lamPi (Term.rename (strengthening.toTermRenaming.lift _)
targetBodyTerm)` whose body's renaming proof has source context
`sourceCtx.cons (targetDomainType.rename strengthening.forward)`,
whereas `bodySound.termRenames` carries the proof at source context
`sourceCtx.cons domainType`.  These are propositionally equal via
`domainRenames : domainType = targetDomainType.rename strengthening.forward`
but Lean's dependent typing rejects them as different types.  Fix:
`subst domainRenames` early to unify the two contexts, then Lean's
definitional proof irrelevance on `TermRenaming : Prop` discharges the
remaining equality. -/
theorem partialStrengthenTypedLamPi_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {targetDomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    {bodyResult :
      StrengtheningResult
        (strengthening.lift domainType targetDomainType
          domainTypeStrengthens) body}
    (bodySound : StrengtheningSoundness bodyResult) :
    StrengtheningSoundness
      (partialStrengthenTypedLamPi domainTypeStrengthens bodyResult) := by
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainTypeStrengthens
  subst domainRenames
  cases bodyResult with
  | mk targetCodomainType targetBodyRaw targetBodyTerm
      codomainTypeStrengthens bodyRawStrengthens codomainTypeRenames
      bodyRawRenames =>
      refine ⟨?_⟩
      have bodyHEq := bodySound.termRenames
      simp only [StrengtheningResult.renamedTarget] at bodyHEq
      simp only [partialStrengthenTypedLamPi, StrengtheningResult.renamedTarget,
        Term.rename]
      exact Term.lamPi_HEq_congr rfl codomainTypeRenames
        bodyRawRenames bodyHEq

/-- Soundness for non-dependent lambda strengthening.

Extends the LamPi `subst-early` recipe with the `.weaken` cast bridge.
Body has type `Term (sourceCtx.cons domainType) codomainType.weaken
bodyRaw`.  `Term.rename` of `Term.lam` (Rename.lean:262-264) introduces
a `Ty.weaken_rename_commute rho codomainType ▸` cast to align the body's
type from `codomainType.weaken.rename rho.lift` to `(codomainType.rename
rho).weaken`.  After `subst domainRenames` + `subst codomainRenames`,
both sides agree on domain and codomain, and the body HEq is bridged
to the casted form via `Term.type_eq_cast_heq`. -/
theorem partialStrengthenTypedLam_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {targetDomainType targetCodomainType : Ty level targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (domainTypeStrengthens :
      domainType.partialStrengthen? strengthening.back =
        some targetDomainType)
    (codomainTypeStrengthens :
      codomainType.partialStrengthen? strengthening.back =
        some targetCodomainType)
    {bodyResult :
      StrengtheningResult
        (strengthening.lift domainType targetDomainType
          domainTypeStrengthens) body}
    (bodySound : StrengtheningSoundness bodyResult) :
    StrengtheningSoundness
      (partialStrengthenTypedLam domainTypeStrengthens
        codomainTypeStrengthens bodyResult) := by
  have domainRenames :
      domainType = targetDomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename domainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetDomainType domainTypeStrengthens
  have codomainRenames :
      codomainType = targetCodomainType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename codomainType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCodomainType codomainTypeStrengthens
  subst domainRenames
  subst codomainRenames
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          Ty.partialStrengthen?
              (Ty.weaken (targetCodomainType.rename strengthening.forward))
              strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have expectedBodyTypeStrengthens :
          Ty.partialStrengthen?
              (Ty.weaken (targetCodomainType.rename strengthening.forward))
              strengthening.back.lift =
            some targetCodomainType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift
          (targetCodomainType.rename strengthening.forward)
          strengthening.back, codomainTypeStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      refine ⟨?_⟩
      have bodyHEq := bodySound.termRenames
      simp only [StrengtheningResult.renamedTarget] at bodyHEq
      simp only [partialStrengthenTypedLam, StrengtheningResult.renamedTarget]
      have castedHEq : HEq body
          (Ty.weaken_rename_commute strengthening.forward
              targetCodomainType ▸
            Term.rename
              ((strengthening.lift (targetDomainType.rename
                  strengthening.forward) targetDomainType
                domainTypeStrengthens).toTermRenaming) targetBodyTerm) :=
        HEq.trans bodyHEq
          (Term.type_eq_cast_heq
            (Ty.weaken_rename_commute strengthening.forward
              targetCodomainType)
            (Term.rename
              ((strengthening.lift (targetDomainType.rename
                  strengthening.forward) targetDomainType
                domainTypeStrengthens).toTermRenaming)
              targetBodyTerm)).symm
      exact Term.lam_HEq_congr rfl rfl bodyRawRenames castedHEq

/-- Soundness for cubical Path-lambda strengthening.

Mirrors `partialStrengthenTypedLam_sound`: pathLam binds `Ty.interval`
(closed, no strengthening dance) and the body's expected type uses
`carrierType.weaken`.  `Term.rename` of `Term.pathLam` introduces the
same `Ty.weaken_rename_commute rho carrierType ▸` cast as Term.lam.

Compared to Lam: only the carrier type is renamed (interval is closed
so no domainRenames step is needed), and three additional explicit
fields — `leftEndpoint`, `rightEndpoint`, the mode-univalent witness —
flow through unchanged because `Ty.path`'s renaming distributes over
them.  `subst carrierRenames` alone replaces `carrierType` with the
renamed target, then the body dance + cast bridge proceeds exactly as
Lam. -/
theorem partialStrengthenTypedPathLam_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (carrierStrengthens :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftEndpointStrengthens :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightEndpointStrengthens :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {bodyResult :
      StrengtheningResult
        (strengthening.lift Ty.interval Ty.interval rfl) body}
    (bodySound : StrengtheningSoundness bodyResult) :
    StrengtheningSoundness
      (partialStrengthenTypedPathLam modeIsUnivalent
        carrierStrengthens leftEndpointStrengthens
        rightEndpointStrengthens bodyResult) := by
  have carrierRenames :
      carrierType = targetCarrierType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierStrengthens
  have leftEndpointRenames :
      leftEndpoint =
        targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftEndpointStrengthens
  have rightEndpointRenames :
      rightEndpoint =
        targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightEndpointStrengthens
  subst carrierRenames
  subst leftEndpointRenames
  subst rightEndpointRenames
  cases bodyResult with
  | mk targetBodyType targetBodyRaw targetBodyTerm bodyTypeStrengthens
      bodyRawStrengthens bodyTypeRenames bodyRawRenames =>
      have bodyTypeStrengthensAtLift :
          Ty.partialStrengthen?
              (Ty.weaken (targetCarrierType.rename strengthening.forward))
              strengthening.back.lift =
            some targetBodyType := by
        simpa only [ContextStrengthening.lift] using bodyTypeStrengthens
      have expectedBodyTypeStrengthens :
          Ty.partialStrengthen?
              (Ty.weaken (targetCarrierType.rename strengthening.forward))
              strengthening.back.lift =
            some targetCarrierType.weaken := by
        rw [Ty.partialStrengthen?_weaken_lift
          (targetCarrierType.rename strengthening.forward)
          strengthening.back, carrierStrengthens]
        rfl
      rw [expectedBodyTypeStrengthens] at bodyTypeStrengthensAtLift
      cases bodyTypeStrengthensAtLift
      refine ⟨?_⟩
      have bodyHEq := bodySound.termRenames
      simp only [StrengtheningResult.renamedTarget] at bodyHEq
      simp only [partialStrengthenTypedPathLam,
        StrengtheningResult.renamedTarget]
      have castedHEq : HEq body
          (Ty.weaken_rename_commute strengthening.forward
              targetCarrierType ▸
            Term.rename
              ((strengthening.lift Ty.interval Ty.interval
                rfl).toTermRenaming) targetBodyTerm) :=
        HEq.trans bodyHEq
          (Term.type_eq_cast_heq
            (Ty.weaken_rename_commute strengthening.forward
              targetCarrierType)
            (Term.rename
              ((strengthening.lift Ty.interval Ty.interval
                rfl).toTermRenaming)
              targetBodyTerm)).symm
      exact Term.pathLam_HEq_congr modeIsUnivalent rfl rfl rfl
        bodyRawRenames castedHEq

/-- Soundness for cubical Glue-elimination strengthening.  Mirrors the
RefineElim/CodataDest OfSuccess pattern: the wrapper's dual
`Option.casesOn` on `Ty.glue`'s base + boundary pivots is replaced by
pre-witnessed `baseSuccess`/`boundarySuccess` in the OfSuccess. -/
theorem partialStrengthenTypedGlueElimOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {targetBaseType : Ty level targetScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {targetBoundaryWitness targetGluedRaw : RawTerm targetScope}
    {gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    {targetGluedValue :
      Term targetCtx (Ty.glue targetBaseType targetBoundaryWitness)
        targetGluedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundarySuccess :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    (gluedRawStrengthens :
      gluedRaw.partialStrengthen? strengthening.back = some targetGluedRaw)
    (gluedRawRenames :
      gluedRaw = targetGluedRaw.rename strengthening.forward)
    (gluedSound :
      HEq gluedValue
        (Term.rename strengthening.toTermRenaming targetGluedValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedGlueElimOfSuccess modeIsUnivalent
        (gluedValue := gluedValue) targetGluedValue baseSuccess
        boundarySuccess gluedRawStrengthens gluedRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedGlueElimOfSuccess]
  have baseRenames :
      baseType = targetBaseType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename baseType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBaseType baseSuccess
  have boundaryRenames :
      boundaryWitness =
        targetBoundaryWitness.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename boundaryWitness
      strengthening.forward strengthening.back strengthening.injectsBack
      targetBoundaryWitness boundarySuccess
  exact Term.glueElim_HEq_congr modeIsUnivalent baseRenames boundaryRenames
    gluedRawRenames gluedSound

/-- Soundness for the typed glue-elimination wrapper.

Mirrors `partialStrengthenTypedGlueElim`'s App-pattern shape: the
wrapper takes `baseSuccess` and `boundarySuccess` as explicit
parameters (lifted from the dispatcher's two nested option-splits on
base type and boundary witness respectively).  The proof destructures
the glued value's `StrengtheningResult`, aligns the `Ty.glue` shape via
`rw` + `cases` on the derived equation, then delegates to
`partialStrengthenTypedGlueElimOfSuccess_sound`.  Same recipe as
Phase 39 RefineElim / Phase 40 CodataDest. -/
theorem partialStrengthenTypedGlueElim_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {targetBaseType : Ty level targetScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {targetBoundaryWitness : RawTerm targetScope}
    {gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (baseSuccess :
      baseType.partialStrengthen? strengthening.back = some targetBaseType)
    (boundarySuccess :
      boundaryWitness.partialStrengthen? strengthening.back =
        some targetBoundaryWitness)
    {gluedResult : StrengtheningResult strengthening gluedValue}
    (gluedSound : StrengtheningSoundness gluedResult) :
    StrengtheningSoundness
      (partialStrengthenTypedGlueElim modeIsUnivalent baseSuccess
        boundarySuccess gluedResult) := by
  cases gluedResult with
  | mk targetGluedType targetGluedRaw targetGluedValue
      gluedTypeStrengthens gluedRawStrengthens gluedTypeRenames
      gluedRawRenames =>
      have expectedGluedTypeStrengthens :
          (Ty.glue baseType boundaryWitness).partialStrengthen?
              strengthening.back =
            some (Ty.glue targetBaseType targetBoundaryWitness) := by
        change
          Option.mapTwo
            (baseType.partialStrengthen? strengthening.back)
            (boundaryWitness.partialStrengthen? strengthening.back)
            Ty.glue =
              some (Ty.glue targetBaseType targetBoundaryWitness)
        rw [baseSuccess, boundarySuccess]
        rfl
      rw [expectedGluedTypeStrengthens] at gluedTypeStrengthens
      cases gluedTypeStrengthens
      exact partialStrengthenTypedGlueElimOfSuccess_sound
        modeIsUnivalent
        (baseSuccess := baseSuccess)
        (boundarySuccess := boundarySuccess)
        (gluedRawStrengthens := gluedRawStrengthens)
        (gluedRawRenames := gluedRawRenames)
        gluedSound.termRenames

/-- Soundness for cubical path-application strengthening (OfSuccess
form).

Mirrors the GlueElim/RefineElim recipe: takes pre-witnessed
strengthening of the path's carrier + left + right endpoints + raw
forms, plus HEq witnesses for the path/interval sub-terms.  Recovers
the syntactic equalities via `partialStrengthen?_imp_rename` and
applies `pathApp_HEq_congr`.

The wrapper `partialStrengthenTypedPathApp` does a dual `Option.casesOn`
on the three Ty.path pivots; the OfSuccess pre-witnesses them, sparing
the soundness proof from re-doing that dance. -/
theorem partialStrengthenTypedPathAppOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {targetPathRaw targetIntervalRaw : RawTerm targetScope}
    {pathTerm :
      Term sourceCtx
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    {targetPathTerm :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetPathRaw}
    {targetIntervalTerm :
      Term targetCtx Ty.interval targetIntervalRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (pathRawStrengthens :
      pathRaw.partialStrengthen? strengthening.back = some targetPathRaw)
    (intervalRawStrengthens :
      intervalRaw.partialStrengthen? strengthening.back =
        some targetIntervalRaw)
    (pathRawRenames :
      pathRaw = targetPathRaw.rename strengthening.forward)
    (intervalRawRenames :
      intervalRaw = targetIntervalRaw.rename strengthening.forward)
    (pathSound :
      HEq pathTerm
        (Term.rename strengthening.toTermRenaming targetPathTerm))
    (intervalSound :
      HEq intervalTerm
        (Term.rename strengthening.toTermRenaming targetIntervalTerm)) :
    StrengtheningSoundness
      (partialStrengthenTypedPathAppOfSuccess modeIsUnivalent
        (pathTerm := pathTerm) (intervalTerm := intervalTerm)
        targetPathTerm targetIntervalTerm carrierSuccess leftSuccess
        rightSuccess pathRawStrengthens intervalRawStrengthens
        pathRawRenames intervalRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedPathAppOfSuccess]
  have carrierRenames :
      carrierType = targetCarrierType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierSuccess
  have leftEndpointRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightEndpointRenames :
      rightEndpoint =
        targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.pathApp_HEq_congr modeIsUnivalent carrierRenames
    leftEndpointRenames rightEndpointRenames pathRawRenames
    intervalRawRenames pathSound intervalSound

/-- Soundness of `partialStrengthenTypedTranspOfSuccess`: the result's
renamed target term is heterogeneously equal to the original typed
transport.  Composes with `Term.transp_HEq_congr` plus
`partialStrengthen?_imp_rename` for the type / raw equalities. -/
theorem partialStrengthenTypedTranspOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {sourceType targetType : Ty level sourceScope}
    {targetSourceType targetTargetType : Ty level targetScope}
    {sourceTypeRaw targetTypeRaw : RawTerm sourceScope}
    {targetSourceTypeRaw targetTargetTypeRaw : RawTerm targetScope}
    {pathRaw sourceRaw : RawTerm sourceScope}
    {targetPathRaw targetSourceRaw : RawTerm targetScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    {targetPath :
      Term targetCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          targetSourceTypeRaw targetTargetTypeRaw)
        targetPathRaw}
    {targetSourceValue :
      Term targetCtx targetSourceType targetSourceRaw}
    (sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (targetTypeRawStrengthens :
      targetTypeRaw.partialStrengthen? strengthening.back =
        some targetTargetTypeRaw)
    (pathRawStrengthens :
      pathRaw.partialStrengthen? strengthening.back =
        some targetPathRaw)
    (sourceRawStrengthens :
      sourceRaw.partialStrengthen? strengthening.back =
        some targetSourceRaw)
    (pathRawRenames :
      pathRaw = targetPathRaw.rename strengthening.forward)
    (sourceRawRenames :
      sourceRaw = targetSourceRaw.rename strengthening.forward)
    (pathSound :
      HEq typePath
        (Term.rename strengthening.toTermRenaming targetPath))
    (sourceSound :
      HEq sourceValue
        (Term.rename strengthening.toTermRenaming targetSourceValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedTranspOfSuccess modeIsUnivalent
        universeLevel universeLevelLt
        (typePath := typePath) (sourceValue := sourceValue)
        targetPath targetSourceValue sourceTypeStrengthens
        targetTypeStrengthens sourceTypeRawStrengthens
        targetTypeRawStrengthens pathRawStrengthens sourceRawStrengthens
        pathRawRenames sourceRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedTranspOfSuccess]
  have sourceTypeRenames :
      sourceType = targetSourceType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename sourceType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetSourceType sourceTypeStrengthens
  have targetTypeRenames :
      targetType = targetTargetType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename targetType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetTargetType targetTypeStrengthens
  have sourceTypeRawRenames :
      sourceTypeRaw =
        targetSourceTypeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename sourceTypeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetSourceTypeRaw sourceTypeRawStrengthens
  have targetTypeRawRenames :
      targetTypeRaw =
        targetTargetTypeRaw.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename targetTypeRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      targetTargetTypeRaw targetTypeRawStrengthens
  exact Term.transp_HEq_congr modeIsUnivalent universeLevel
    universeLevelLt sourceTypeRenames targetTypeRenames
    sourceTypeRawRenames targetTypeRawRenames pathRawRenames
    sourceRawRenames pathSound sourceSound

/-- Soundness for the typed-transport strengthening wrapper.

The wrapper inline-constructs a `StrengtheningResult` after splitting the
path and source-value results.  This soundness mirror parallels those
splits, aligns the path type via the expected path-strengthening
equation, and discharges via `Term.transp_HEq_congr`. -/
theorem partialStrengthenTypedTransp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (targetSourceType targetTargetType : Ty level targetScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    (targetSourceTypeRaw targetTargetTypeRaw : RawTerm targetScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (sourceTypeStrengthens :
      sourceType.partialStrengthen? strengthening.back =
        some targetSourceType)
    (targetTypeStrengthens :
      targetType.partialStrengthen? strengthening.back =
        some targetTargetType)
    (sourceTypeRawStrengthens :
      sourceTypeRaw.partialStrengthen? strengthening.back =
        some targetSourceTypeRaw)
    (targetTypeRawStrengthens :
      targetTypeRaw.partialStrengthen? strengthening.back =
        some targetTargetTypeRaw)
    {pathResult : StrengtheningResult strengthening typePath}
    {sourceResult : StrengtheningResult strengthening sourceValue}
    (pathSound : StrengtheningSoundness pathResult)
    (sourceSound : StrengtheningSoundness sourceResult) :
    StrengtheningSoundness
      (partialStrengthenTypedTransp modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType targetSourceType
        targetTargetType sourceTypeRaw targetTypeRaw
        targetSourceTypeRaw targetTargetTypeRaw
        sourceTypeStrengthens targetTypeStrengthens
        sourceTypeRawStrengthens targetTypeRawStrengthens
        pathResult sourceResult) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPath pathTypeStrengthens
      pathRawStrengthens pathTypeRenames pathRawRenames =>
      have expectedPathTypeStrengthens :
          (Ty.path (Ty.universe universeLevel universeLevelLt)
              sourceTypeRaw targetTypeRaw).partialStrengthen?
              strengthening.back =
            some (Ty.path (Ty.universe universeLevel universeLevelLt)
              targetSourceTypeRaw targetTargetTypeRaw) := by
        change
          Option.mapThree
            ((Ty.universe universeLevel universeLevelLt).partialStrengthen?
              strengthening.back)
            (sourceTypeRaw.partialStrengthen? strengthening.back)
            (targetTypeRaw.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path (Ty.universe universeLevel universeLevelLt)
                targetSourceTypeRaw targetTargetTypeRaw)
        rw [sourceTypeRawStrengthens, targetTypeRawStrengthens]
        rfl
      rw [expectedPathTypeStrengthens] at pathTypeStrengthens
      cases pathTypeStrengthens
      cases sourceResult with
      | mk targetSourceValueType targetSourceRaw targetSourceValue
          sourceValueTypeStrengthens sourceRawStrengthens
          sourceValueTypeRenames sourceRawRenames =>
          rw [sourceTypeStrengthens] at sourceValueTypeStrengthens
          cases sourceValueTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedTransp,
              StrengtheningResult.renamedTarget]
            at pathSound sourceSound ⊢
          have sourceTypeRenames :
              sourceType = targetSourceType.rename strengthening.forward :=
            Ty.partialStrengthen?_imp_rename sourceType
              strengthening.forward strengthening.back
              strengthening.injectsBack targetSourceType
              sourceTypeStrengthens
          have targetTypeRenames :
              targetType = targetTargetType.rename strengthening.forward :=
            Ty.partialStrengthen?_imp_rename targetType
              strengthening.forward strengthening.back
              strengthening.injectsBack targetTargetType
              targetTypeStrengthens
          have sourceTypeRawRenames :
              sourceTypeRaw =
                targetSourceTypeRaw.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename sourceTypeRaw
              strengthening.forward strengthening.back
              strengthening.injectsBack targetSourceTypeRaw
              sourceTypeRawStrengthens
          have targetTypeRawRenames :
              targetTypeRaw =
                targetTargetTypeRaw.rename strengthening.forward :=
            RawTerm.partialStrengthen?_imp_rename targetTypeRaw
              strengthening.forward strengthening.back
              strengthening.injectsBack targetTargetTypeRaw
              targetTypeRawStrengthens
          exact Term.transp_HEq_congr modeIsUnivalent universeLevel
            universeLevelLt sourceTypeRenames targetTypeRenames
            sourceTypeRawRenames targetTypeRawRenames pathRawRenames
            sourceRawRenames pathSound.termRenames
            sourceSound.termRenames

/-- Soundness of `partialStrengthenTypedHcompOfSuccess`: the result's
renamed target term is heterogeneously equal to the original typed
homogeneous composition. -/
theorem partialStrengthenTypedHcompOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {targetSidesRaw targetCapRaw : RawTerm targetScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    {targetSidesValue :
      Term targetCtx targetCarrierType targetSidesRaw}
    {targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw}
    (carrierStrengthens :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (sidesRawStrengthens :
      sidesRaw.partialStrengthen? strengthening.back =
        some targetSidesRaw)
    (capRawStrengthens :
      capRaw.partialStrengthen? strengthening.back =
        some targetCapRaw)
    (sidesRawRenames :
      sidesRaw = targetSidesRaw.rename strengthening.forward)
    (capRawRenames :
      capRaw = targetCapRaw.rename strengthening.forward)
    (sidesSound :
      HEq sidesValue
        (Term.rename strengthening.toTermRenaming targetSidesValue))
    (capSound :
      HEq capValue
        (Term.rename strengthening.toTermRenaming targetCapValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedHcompOfSuccess modeIsUnivalent
        (sidesValue := sidesValue) (capValue := capValue)
        targetSidesValue targetCapValue carrierStrengthens
        sidesRawStrengthens capRawStrengthens sidesRawRenames
        capRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedHcompOfSuccess]
  have carrierRenames :
      carrierType = targetCarrierType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierStrengthens
  exact Term.hcomp_HEq_congr modeIsUnivalent carrierRenames
    sidesRawRenames capRawRenames sidesSound capSound

/-- Soundness for the typed homogeneous-composition wrapper.

Mirrors `partialStrengthenTypedHcomp`'s inline-construct pattern:
splits both child results, aligns the cap type via the sides'
carrier-type strengthening, and discharges via `Term.hcomp_HEq_congr`. -/
theorem partialStrengthenTypedHcomp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    {sidesResult : StrengtheningResult strengthening sidesValue}
    {capResult : StrengtheningResult strengthening capValue}
    (sidesSound : StrengtheningSoundness sidesResult)
    (capSound : StrengtheningSoundness capResult) :
    StrengtheningSoundness
      (partialStrengthenTypedHcomp modeIsUnivalent sidesResult
        capResult) := by
  cases sidesResult with
  | mk targetCarrierType targetSidesRaw targetSidesValue
      carrierStrengthens sidesRawStrengthens carrierRenames
      sidesRawRenames =>
      cases capResult with
      | mk targetCapType targetCapRaw targetCapValue capTypeStrengthens
          capRawStrengthens capTypeRenames capRawRenames =>
          rw [carrierStrengthens] at capTypeStrengthens
          cases capTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedHcomp,
              StrengtheningResult.renamedTarget]
            at sidesSound capSound ⊢
          exact Term.hcomp_HEq_congr modeIsUnivalent carrierRenames
            sidesRawRenames capRawRenames sidesSound.termRenames
            capSound.termRenames

/-- Soundness of `partialStrengthenTypedHcompPathOfSuccess`: the
result's renamed target term is heterogeneously equal to the original
typed path-shaped homogeneous composition. -/
theorem partialStrengthenTypedHcompPathOfSuccess_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {targetSidesPathRaw targetCapRaw : RawTerm targetScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    {targetSidesPath :
      Term targetCtx
        (Ty.path targetCarrierType targetLeftEndpoint targetRightEndpoint)
        targetSidesPathRaw}
    {targetCapValue :
      Term targetCtx targetCarrierType targetCapRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    (sidesPathRawStrengthens :
      sidesPathRaw.partialStrengthen? strengthening.back =
        some targetSidesPathRaw)
    (capRawStrengthens :
      capRaw.partialStrengthen? strengthening.back =
        some targetCapRaw)
    (sidesPathRawRenames :
      sidesPathRaw = targetSidesPathRaw.rename strengthening.forward)
    (capRawRenames :
      capRaw = targetCapRaw.rename strengthening.forward)
    (sidesPathSound :
      HEq sidesPath
        (Term.rename strengthening.toTermRenaming targetSidesPath))
    (capSound :
      HEq capValue
        (Term.rename strengthening.toTermRenaming targetCapValue)) :
    StrengtheningSoundness
      (partialStrengthenTypedHcompPathOfSuccess modeIsUnivalent
        leftEndpoint rightEndpoint
        (sidesPath := sidesPath) (capValue := capValue)
        targetSidesPath targetCapValue carrierSuccess leftSuccess
        rightSuccess sidesPathRawStrengthens capRawStrengthens
        sidesPathRawRenames capRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedHcompPathOfSuccess]
  have carrierRenames :
      carrierType = targetCarrierType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierType
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierType carrierSuccess
  have leftEndpointRenames :
      leftEndpoint = targetLeftEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename leftEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetLeftEndpoint leftSuccess
  have rightEndpointRenames :
      rightEndpoint =
        targetRightEndpoint.rename strengthening.forward :=
    RawTerm.partialStrengthen?_imp_rename rightEndpoint
      strengthening.forward strengthening.back strengthening.injectsBack
      targetRightEndpoint rightSuccess
  exact Term.hcompPath_HEq_congr modeIsUnivalent carrierRenames
    leftEndpointRenames rightEndpointRenames sidesPathRawRenames
    capRawRenames sidesPathSound capSound

/-- Soundness of the App-pattern `partialStrengthenTypedHcompPath`
wrapper: destructures both child `StrengtheningResult`s, aligns the
`Ty.path` shape of the sides path's type and the `carrierType` of the
cap, then delegates to `_OfSuccess_sound`.

Mirrors the wrapper's cascade exactly: 3 type/raw witnesses
(`carrierSuccess`/`leftSuccess`/`rightSuccess`) lifted from the
dispatcher to the wrapper become explicit parameters here.  The
`Option.mapThree` shape of the sides path type discharge uses the
same `change`+`rw [carrierSuccess, leftSuccess, rightSuccess]; rfl`
recipe as the wrapper.  Extends the Phase 39/40/41 (2-option) pattern
to 3-option wrappers; child soundness HEqs extracted via
`.termRenames` projection. -/
theorem partialStrengthenTypedHcompPath_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {sidesPathResult : StrengtheningResult strengthening sidesPath}
    {capResult : StrengtheningResult strengthening capValue}
    (sidesPathSound : StrengtheningSoundness sidesPathResult)
    (capSound : StrengtheningSoundness capResult) :
    StrengtheningSoundness
      (partialStrengthenTypedHcompPath modeIsUnivalent leftEndpoint
        rightEndpoint carrierSuccess leftSuccess rightSuccess
        sidesPathResult capResult) := by
  cases sidesPathResult with
  | mk targetSidesPathType targetSidesPathRaw targetSidesPath
      sidesPathTypeStrengthens sidesPathRawStrengthens
      sidesPathTypeRenames sidesPathRawRenames =>
      have expectedSidesPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint
              rightEndpoint).partialStrengthen?
              strengthening.back =
            some (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint) := by
        change
          Option.mapThree
            (carrierType.partialStrengthen? strengthening.back)
            (leftEndpoint.partialStrengthen? strengthening.back)
            (rightEndpoint.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
        rw [carrierSuccess, leftSuccess, rightSuccess]
        rfl
      rw [expectedSidesPathTypeStrengthens] at sidesPathTypeStrengthens
      cases sidesPathTypeStrengthens
      cases capResult with
      | mk targetCapType targetCapRaw targetCapValue
          capTypeStrengthens capRawStrengthens capTypeRenames
          capRawRenames =>
          rw [carrierSuccess] at capTypeStrengthens
          cases capTypeStrengthens
          exact partialStrengthenTypedHcompPathOfSuccess_sound
            modeIsUnivalent leftEndpoint rightEndpoint
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (sidesPathRawStrengthens := sidesPathRawStrengthens)
            (capRawStrengthens := capRawStrengthens)
            (sidesPathRawRenames := sidesPathRawRenames)
            (capRawRenames := capRawRenames)
            sidesPathSound.termRenames capSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedPathApp`
wrapper.  Cubical path application: takes the three path-type pivots
(`carrierSuccess`/`leftSuccess`/`rightSuccess`) as wrapper parameters
lifted from the dispatcher.  Mirrors the wrapper's cascade — first
`cases` the `pathResult`, align the `Ty.path` shape via
`Option.mapThree` + `rw + rfl`, then `cases` the `intervalResult`
(which always strengthens to `Ty.interval` trivially since the
strengthening preserves `Ty.interval`), and delegate to
`_OfSuccess_sound`.  Companion of Phase 42's HcompPath soundness:
both ship 3-option-split soundness over the same `Ty.path` pivots,
exercising the App-pattern's uniform scaling across cubical
path-eliminators. -/
theorem partialStrengthenTypedPathApp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {targetCarrierType : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {pathTerm : Term sourceCtx
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (carrierSuccess :
      carrierType.partialStrengthen? strengthening.back =
        some targetCarrierType)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {pathResult : StrengtheningResult strengthening pathTerm}
    {intervalResult : StrengtheningResult strengthening intervalTerm}
    (pathSound : StrengtheningSoundness pathResult)
    (intervalSound : StrengtheningSoundness intervalResult) :
    StrengtheningSoundness
      (partialStrengthenTypedPathApp modeIsUnivalent carrierSuccess
        leftSuccess rightSuccess pathResult intervalResult) := by
  cases pathResult with
  | mk targetPathType targetPathRaw targetPathTerm pathTypeStrengthens
      pathRawStrengthens pathTypeRenames pathRawRenames =>
      have expectedPathTypeStrengthens :
          (Ty.path carrierType leftEndpoint
              rightEndpoint).partialStrengthen?
              strengthening.back =
            some (Ty.path targetCarrierType targetLeftEndpoint
              targetRightEndpoint) := by
        change
          Option.mapThree
            (carrierType.partialStrengthen? strengthening.back)
            (leftEndpoint.partialStrengthen? strengthening.back)
            (rightEndpoint.partialStrengthen? strengthening.back)
            Ty.path =
              some (Ty.path targetCarrierType targetLeftEndpoint
                targetRightEndpoint)
        rw [carrierSuccess, leftSuccess, rightSuccess]
        rfl
      rw [expectedPathTypeStrengthens] at pathTypeStrengthens
      cases pathTypeStrengthens
      cases intervalResult with
      | mk targetIntervalType targetIntervalRaw targetIntervalTerm
          intervalTypeStrengthens intervalRawStrengthens
          intervalTypeRenames intervalRawRenames =>
          cases intervalTypeStrengthens
          exact partialStrengthenTypedPathAppOfSuccess_sound
            modeIsUnivalent
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (pathRawStrengthens := pathRawStrengthens)
            (intervalRawStrengthens := intervalRawStrengthens)
            (pathRawRenames := pathRawRenames)
            (intervalRawRenames := intervalRawRenames)
            pathSound.termRenames intervalSound.termRenames

/-- Soundness of `partialStrengthenTypedEquivIntroHetOfSuccess`: the
result's renamed target term is heterogeneously equal to the original
typed heterogeneous-equivalence introduction.  Note: the leftInv and
rightInv raw rename equations are taken as direct inputs since the
typed proof children carry independent raw forms not derivable from
`forwardRaw` / `backwardRaw` alone. -/
theorem partialStrengthenTypedEquivIntroHetOfSuccess_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {targetForwardRaw targetBackwardRaw : RawTerm targetScope}
    {targetLeftInvRaw targetRightInvRaw : RawTerm targetScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    {targetForward :
      Term targetCtx (Ty.arrow targetCarrierA targetCarrierB)
        targetForwardRaw}
    {targetBackward :
      Term targetCtx (Ty.arrow targetCarrierB targetCarrierA)
        targetBackwardRaw}
    {targetLeftInv :
      Term targetCtx
        (equivIntroHetLeftInverseType targetCarrierA targetForwardRaw
          targetBackwardRaw)
        targetLeftInvRaw}
    {targetRightInv :
      Term targetCtx
        (equivIntroHetRightInverseType targetCarrierB targetForwardRaw
          targetBackwardRaw)
        targetRightInvRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back =
        some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back =
        some targetCarrierB)
    (forwardRawStrengthens :
      forwardRaw.partialStrengthen? strengthening.back =
        some targetForwardRaw)
    (backwardRawStrengthens :
      backwardRaw.partialStrengthen? strengthening.back =
        some targetBackwardRaw)
    (forwardRawRenames :
      forwardRaw = targetForwardRaw.rename strengthening.forward)
    (backwardRawRenames :
      backwardRaw = targetBackwardRaw.rename strengthening.forward)
    (leftInvRawRenames :
      leftInvRaw = targetLeftInvRaw.rename strengthening.forward)
    (rightInvRawRenames :
      rightInvRaw = targetRightInvRaw.rename strengthening.forward)
    (forwardSound :
      HEq forward
        (Term.rename strengthening.toTermRenaming targetForward))
    (backwardSound :
      HEq backward
        (Term.rename strengthening.toTermRenaming targetBackward))
    (leftInvSound :
      HEq leftInv
        (Term.rename strengthening.toTermRenaming targetLeftInv))
    (rightInvSound :
      HEq rightInv
        (Term.rename strengthening.toTermRenaming targetRightInv)) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivIntroHetOfSuccess
        (forward := forward) (backward := backward)
        (leftInv := leftInv) (rightInv := rightInv)
        targetForward targetBackward targetLeftInv targetRightInv
        carrierASuccess carrierBSuccess forwardRawStrengthens
        backwardRawStrengthens forwardRawRenames backwardRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEquivIntroHetOfSuccess]
  have carrierARenames :
      carrierA = targetCarrierA.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierA
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierA carrierASuccess
  have carrierBRenames :
      carrierB = targetCarrierB.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  have castedLeftInvSound :
      HEq leftInv
        (equivIntroHetLeftInverseType_rename strengthening.forward
            targetCarrierA targetForwardRaw targetBackwardRaw ▸
          Term.rename strengthening.toTermRenaming targetLeftInv) :=
    HEq.trans leftInvSound
      (Term.type_eq_cast_heq
        (equivIntroHetLeftInverseType_rename strengthening.forward
          targetCarrierA targetForwardRaw targetBackwardRaw)
        (Term.rename strengthening.toTermRenaming targetLeftInv)).symm
  have castedRightInvSound :
      HEq rightInv
        (equivIntroHetRightInverseType_rename strengthening.forward
            targetCarrierB targetForwardRaw targetBackwardRaw ▸
          Term.rename strengthening.toTermRenaming targetRightInv) :=
    HEq.trans rightInvSound
      (Term.type_eq_cast_heq
        (equivIntroHetRightInverseType_rename strengthening.forward
          targetCarrierB targetForwardRaw targetBackwardRaw)
        (Term.rename strengthening.toTermRenaming targetRightInv)).symm
  exact Term.equivIntroHet_HEq_congr carrierARenames carrierBRenames
    forwardRawRenames backwardRawRenames leftInvRawRenames
    rightInvRawRenames forwardSound backwardSound castedLeftInvSound
    castedRightInvSound

/-- Soundness of `partialStrengthenTypedEffectPerformOfSuccess`: the
result's renamed target term is heterogeneously equal to the original
typed effect-performance application.  The proof leans on
proof-irrelevance for `Effects.CanPerform` (a `Prop`-valued inductive)
to align the source's `canPerformOperation` with the renamed target
`CanPerform.map ... targetCanPerform` after operation-signature
carriers are identified via `Ty.partialStrengthen?_imp_rename`. -/
theorem partialStrengthenTypedEffectPerformOfSuccess_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {effectTag : RawTerm sourceScope}
    {targetEffectTag : RawTerm targetScope}
    (effectRow : Effects.EffectRow)
    (operationSignature :
      Effects.OperationSignature (Ty level sourceScope))
    {targetArgumentCarrier targetResultCarrier :
      Ty level targetScope}
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {targetOperationRaw targetArgumentsRaw : RawTerm targetScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    {targetOperationTag :
      Term targetCtx
        (Ty.effect targetArgumentCarrier targetEffectTag)
        targetOperationRaw}
    {targetArguments :
      Term targetCtx targetArgumentCarrier targetArgumentsRaw}
    (effectTagStrengthens :
      effectTag.partialStrengthen? strengthening.back =
        some targetEffectTag)
    (argumentCarrierStrengthens :
      operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back =
        some targetArgumentCarrier)
    (resultCarrierStrengthens :
      operationSignature.resultCarrier.partialStrengthen?
          strengthening.back =
        some targetResultCarrier)
    (operationRawStrengthens :
      operationRaw.partialStrengthen? strengthening.back =
        some targetOperationRaw)
    (argumentsRawStrengthens :
      argumentsRaw.partialStrengthen? strengthening.back =
        some targetArgumentsRaw)
    (effectTagRenames :
      effectTag = targetEffectTag.rename strengthening.forward)
    (operationRawRenames :
      operationRaw = targetOperationRaw.rename strengthening.forward)
    (argumentsRawRenames :
      argumentsRaw = targetArgumentsRaw.rename strengthening.forward)
    (operationTagSound :
      HEq operationTag
        (Term.rename strengthening.toTermRenaming targetOperationTag))
    (argumentsSound :
      HEq arguments
        (Term.rename strengthening.toTermRenaming targetArguments)) :
    StrengtheningSoundness
      (partialStrengthenTypedEffectPerformOfSuccess
        (effectTag := effectTag) (targetEffectTag := targetEffectTag)
        (operationTag := operationTag) (arguments := arguments)
        effectRow operationSignature
        (targetArgumentCarrier := targetArgumentCarrier)
        (targetResultCarrier := targetResultCarrier)
        canPerformOperation targetOperationTag targetArguments
        effectTagStrengthens argumentCarrierStrengthens
        resultCarrierStrengthens operationRawStrengthens
        argumentsRawStrengthens effectTagRenames operationRawRenames
        argumentsRawRenames) := by
  refine ⟨?_⟩
  have argumentCarrierRenames :
      operationSignature.argumentCarrier =
        targetArgumentCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename operationSignature.argumentCarrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetArgumentCarrier argumentCarrierStrengthens
  have resultCarrierRenames :
      operationSignature.resultCarrier =
        targetResultCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename operationSignature.resultCarrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetResultCarrier resultCarrierStrengthens
  obtain ⟨opLabel, opArgCarrier, opResCarrier⟩ := operationSignature
  simp only at argumentCarrierRenames resultCarrierRenames
  subst argumentCarrierRenames
  subst resultCarrierRenames
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEffectPerformOfSuccess]
  cases canPerformOperation with
  | direct rowMember =>
      exact Term.effectPerform_HEq_congr effectRow
        { effectLabel := opLabel
          argumentCarrier :=
            targetArgumentCarrier.rename strengthening.forward
          resultCarrier :=
            targetResultCarrier.rename strengthening.forward }
        (Effects.CanPerform.direct rowMember)
        effectTagRenames operationRawRenames argumentsRawRenames
        operationTagSound argumentsSound
  | readViaWrite _ _ rowMember =>
      exact Term.effectPerform_HEq_congr effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier :=
            targetArgumentCarrier.rename strengthening.forward
          resultCarrier :=
            targetResultCarrier.rename strengthening.forward }
        (Effects.CanPerform.readViaWrite
          (targetArgumentCarrier.rename strengthening.forward)
          (targetResultCarrier.rename strengthening.forward)
          rowMember)
        effectTagRenames operationRawRenames argumentsRawRenames
        operationTagSound argumentsSound

/-- Soundness for the typed effect-performance wrapper.

Mirrors `partialStrengthenTypedEffectPerform`'s structure:
destructures both child `StrengtheningResult` records, aligns the
`Ty.effect`-shaped operation-tag type and the operation-signature
argument-carrier for the arguments-term type, then delegates the
final `HEq` reconstruction to
`partialStrengthenTypedEffectPerformOfSuccess_sound`.  The wrapper
takes `effectTagStrengthens` + `argumentCarrierStrengthens` +
`resultCarrierStrengthens` as explicit parameters; the soundness
theorem threads them straight through. -/
theorem partialStrengthenTypedEffectPerform_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (effectTag : RawTerm sourceScope)
    (targetEffectTag : RawTerm targetScope)
    (effectRow : Effects.EffectRow)
    (operationSignature :
      Effects.OperationSignature (Ty level sourceScope))
    (targetArgumentCarrier targetResultCarrier :
      Ty level targetScope)
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (effectTagStrengthens :
      effectTag.partialStrengthen? strengthening.back =
        some targetEffectTag)
    (argumentCarrierStrengthens :
      operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back =
        some targetArgumentCarrier)
    (resultCarrierStrengthens :
      operationSignature.resultCarrier.partialStrengthen?
          strengthening.back =
        some targetResultCarrier)
    {operationTagResult : StrengtheningResult strengthening operationTag}
    {argumentsResult : StrengtheningResult strengthening arguments}
    (operationTagSound : StrengtheningSoundness operationTagResult)
    (argumentsSound : StrengtheningSoundness argumentsResult)
    (effectTagRenames :
      effectTag = targetEffectTag.rename strengthening.forward) :
    StrengtheningSoundness
      (partialStrengthenTypedEffectPerform effectTag targetEffectTag
        effectRow operationSignature targetArgumentCarrier
        targetResultCarrier canPerformOperation effectTagStrengthens
        argumentCarrierStrengthens resultCarrierStrengthens
        operationTagResult argumentsResult) := by
  cases operationTagResult with
  | mk targetOperationTagType targetOperationRaw targetOperationTag
      operationTagTypeStrengthens operationRawStrengthens
      operationTagTypeRenames operationRawRenames =>
      have expectedOperationTagTypeStrengthens :
          (Ty.effect operationSignature.argumentCarrier
              effectTag).partialStrengthen? strengthening.back =
            some (Ty.effect targetArgumentCarrier targetEffectTag) := by
        change
          Option.mapTwo
            (operationSignature.argumentCarrier.partialStrengthen?
              strengthening.back)
            (effectTag.partialStrengthen? strengthening.back)
            Ty.effect =
              some (Ty.effect targetArgumentCarrier targetEffectTag)
        rw [argumentCarrierStrengthens, effectTagStrengthens]
        rfl
      rw [expectedOperationTagTypeStrengthens]
        at operationTagTypeStrengthens
      cases operationTagTypeStrengthens
      cases argumentsResult with
      | mk targetArgumentsType targetArgumentsRaw targetArguments
          argumentsTypeStrengthens argumentsRawStrengthens
          argumentsTypeRenames argumentsRawRenames =>
          rw [argumentCarrierStrengthens] at argumentsTypeStrengthens
          cases argumentsTypeStrengthens
          exact partialStrengthenTypedEffectPerformOfSuccess_sound
            effectRow operationSignature canPerformOperation
            (targetOperationTag := targetOperationTag)
            (targetArguments := targetArguments)
            effectTagStrengthens argumentCarrierStrengthens
            resultCarrierStrengthens operationRawStrengthens
            argumentsRawStrengthens effectTagRenames
            operationRawRenames argumentsRawRenames
            operationTagSound.termRenames
            argumentsSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedListElim`
wrapper.  Cases the three subterm results, aligns each list/arrow type
shape via `Option.mapTwo`/`match` rewriting on the pivot
`elementSuccess`, and delegates to `_OfSuccess_sound` with the cascade
of `.termRenames` HEq witnesses. -/
theorem partialStrengthenTypedListElim_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {targetElementType : Ty level targetScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType)
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {nilResult : StrengtheningResult strengthening nilBranch}
    {consResult : StrengtheningResult strengthening consBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (nilSound : StrengtheningSoundness nilResult)
    (consSound : StrengtheningSoundness consResult) :
    StrengtheningSoundness
      (partialStrengthenTypedListElim elementSuccess scrutineeResult
        nilResult consResult) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      have expectedScrutineeTypeStrengthens :
          (Ty.listType elementType).partialStrengthen?
              strengthening.back =
            some (Ty.listType targetElementType) := by
        change
          (match elementType.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (Ty.listType strengthenedElement)
          | none => none) = some (Ty.listType targetElementType)
        rw [elementSuccess]
      rw [expectedScrutineeTypeStrengthens] at scrutineeTypeStrengthens
      cases scrutineeTypeStrengthens
      cases nilResult with
      | mk targetMotiveType targetNilRaw targetNilTerm
          nilTypeStrengthens nilRawStrengthens nilTypeRenames
          nilRawRenames =>
          cases consResult with
          | mk targetConsType targetConsRaw targetConsTerm
              consTypeStrengthens consRawStrengthens consTypeRenames
              consRawRenames =>
              change
                Option.mapTwo
                  (elementType.partialStrengthen? strengthening.back)
                  (Option.mapTwo
                    (match elementType.partialStrengthen?
                        strengthening.back with
                    | some strengthenedElement =>
                        some (Ty.listType strengthenedElement)
                    | none => none)
                    (motiveType.partialStrengthen? strengthening.back)
                    Ty.arrow)
                  Ty.arrow = some targetConsType at consTypeStrengthens
              rw [elementSuccess, nilTypeStrengthens] at consTypeStrengthens
              cases consTypeStrengthens
              exact partialStrengthenTypedListElimOfSuccess_sound
                (scrutinee := scrutinee) (nilBranch := nilBranch)
                (consBranch := consBranch)
                (elementSuccess := elementSuccess)
                (motiveSuccess := nilTypeStrengthens)
                (scrutineeRawStrengthens := scrutineeRawStrengthens)
                (nilRawStrengthens := nilRawStrengthens)
                (consRawStrengthens := consRawStrengthens)
                (scrutineeRawRenames := scrutineeRawRenames)
                (nilRawRenames := nilRawRenames)
                (consRawRenames := consRawRenames)
                scrutineeSound.termRenames nilSound.termRenames
                consSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedOptionMatch`
wrapper.  Sister of `partialStrengthenTypedListElim_sound`: same
single-pivot (`elementSuccess`) cascade over `Ty.optionType` and the
some-branch `Ty.arrow`. -/
theorem partialStrengthenTypedOptionMatch_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {targetElementType : Ty level targetScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (elementSuccess :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType)
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {noneResult : StrengtheningResult strengthening noneBranch}
    {someResult : StrengtheningResult strengthening someBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (noneSound : StrengtheningSoundness noneResult)
    (someSound : StrengtheningSoundness someResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionMatch elementSuccess scrutineeResult
        noneResult someResult) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      have expectedScrutineeTypeStrengthens :
          (Ty.optionType elementType).partialStrengthen?
              strengthening.back =
            some (Ty.optionType targetElementType) := by
        change
          (match elementType.partialStrengthen? strengthening.back with
          | some strengthenedElement =>
              some (Ty.optionType strengthenedElement)
          | none => none) = some (Ty.optionType targetElementType)
        rw [elementSuccess]
      rw [expectedScrutineeTypeStrengthens] at scrutineeTypeStrengthens
      cases scrutineeTypeStrengthens
      cases noneResult with
      | mk targetMotiveType targetNoneRaw targetNoneTerm
          noneTypeStrengthens noneRawStrengthens noneTypeRenames
          noneRawRenames =>
          cases someResult with
          | mk targetSomeType targetSomeRaw targetSomeTerm
              someTypeStrengthens someRawStrengthens someTypeRenames
              someRawRenames =>
              change
                Option.mapTwo
                  (elementType.partialStrengthen? strengthening.back)
                  (motiveType.partialStrengthen? strengthening.back)
                  Ty.arrow = some targetSomeType at someTypeStrengthens
              rw [elementSuccess, noneTypeStrengthens] at someTypeStrengthens
              cases someTypeStrengthens
              exact partialStrengthenTypedOptionMatchOfSuccess_sound
                (scrutinee := scrutinee) (noneBranch := noneBranch)
                (someBranch := someBranch)
                (elementSuccess := elementSuccess)
                (motiveSuccess := noneTypeStrengthens)
                (scrutineeRawStrengthens := scrutineeRawStrengthens)
                (noneRawStrengthens := noneRawStrengthens)
                (someRawStrengthens := someRawStrengthens)
                (scrutineeRawRenames := scrutineeRawRenames)
                (noneRawRenames := noneRawRenames)
                (someRawRenames := someRawRenames)
                scrutineeSound.termRenames noneSound.termRenames
                someSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEitherMatch`
wrapper.  Triple-pivot cascade (`leftSuccess`/`rightSuccess`/`motiveSuccess`)
threads through `Ty.eitherType` decomposition and both branch
`Ty.arrow` shapes. -/
theorem partialStrengthenTypedEitherMatch_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {targetLeftType targetRightType targetMotiveType : Ty level targetScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (leftSuccess :
      leftType.partialStrengthen? strengthening.back = some targetLeftType)
    (rightSuccess :
      rightType.partialStrengthen? strengthening.back = some targetRightType)
    (motiveSuccess :
      motiveType.partialStrengthen? strengthening.back =
        some targetMotiveType)
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {leftResult : StrengtheningResult strengthening leftBranch}
    {rightResult : StrengtheningResult strengthening rightBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (leftSound : StrengtheningSoundness leftResult)
    (rightSound : StrengtheningSoundness rightResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEitherMatch leftSuccess rightSuccess
        motiveSuccess scrutineeResult leftResult rightResult) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      have expectedScrutineeTypeStrengthens :
          (Ty.eitherType leftType rightType).partialStrengthen?
              strengthening.back =
            some (Ty.eitherType targetLeftType targetRightType) := by
        change
          Option.mapTwo
            (leftType.partialStrengthen? strengthening.back)
            (rightType.partialStrengthen? strengthening.back)
            Ty.eitherType =
              some (Ty.eitherType targetLeftType targetRightType)
        rw [leftSuccess, rightSuccess]
        rfl
      rw [expectedScrutineeTypeStrengthens] at scrutineeTypeStrengthens
      cases scrutineeTypeStrengthens
      cases leftResult with
      | mk targetLeftBranchType targetLeftRaw targetLeftTerm
          leftTypeStrengthens leftRawStrengthens leftTypeRenames
          leftRawRenames =>
          change
            Option.mapTwo
              (leftType.partialStrengthen? strengthening.back)
              (motiveType.partialStrengthen? strengthening.back)
              Ty.arrow = some targetLeftBranchType at leftTypeStrengthens
          rw [leftSuccess, motiveSuccess] at leftTypeStrengthens
          cases leftTypeStrengthens
          cases rightResult with
          | mk targetRightBranchType targetRightRaw
              targetRightTerm rightTypeStrengthens
              rightRawStrengthens rightTypeRenames
              rightRawRenames =>
              change
                Option.mapTwo
                  (rightType.partialStrengthen?
                    strengthening.back)
                  (motiveType.partialStrengthen?
                    strengthening.back)
                  Ty.arrow = some targetRightBranchType at rightTypeStrengthens
              rw [rightSuccess, motiveSuccess] at rightTypeStrengthens
              cases rightTypeStrengthens
              exact partialStrengthenTypedEitherMatchOfSuccess_sound
                (scrutinee := scrutinee) (leftBranch := leftBranch)
                (rightBranch := rightBranch)
                (leftSuccess := leftSuccess)
                (rightSuccess := rightSuccess)
                (motiveSuccess := motiveSuccess)
                (scrutineeRawStrengthens := scrutineeRawStrengthens)
                (leftRawStrengthens := leftRawStrengthens)
                (rightRawStrengthens := rightRawStrengthens)
                (scrutineeRawRenames := scrutineeRawRenames)
                (leftRawRenames := leftRawRenames)
                (rightRawRenames := rightRawRenames)
                scrutineeSound.termRenames leftSound.termRenames
                rightSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedIdJ` wrapper.
Triple-pivot cascade (`carrierSuccess`/`leftSuccess`/`rightSuccess`)
threads through `Ty.id` decomposition on the witness child. -/
theorem partialStrengthenTypedIdJ_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {baseResult : StrengtheningResult strengthening baseCase}
    {witnessResult : StrengtheningResult strengthening witness}
    (baseSound : StrengtheningSoundness baseResult)
    (witnessSound : StrengtheningSoundness witnessResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIdJ carrierSuccess leftSuccess rightSuccess
        baseResult witnessResult) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.id carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.id targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.id =
                  some (Ty.id targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedIdJOfSuccess_sound
            (baseCase := baseCase) (witness := witness)
            (baseTypeStrengthens := baseTypeStrengthens)
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (baseRawStrengthens := baseRawStrengthens)
            (witnessRawStrengthens := witnessRawStrengthens)
            (baseTypeRenames := baseTypeRenames)
            (baseRawRenames := baseRawRenames)
            (witnessRawRenames := witnessRawRenames)
            baseSound.termRenames witnessSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedOeqJ` wrapper.
Mirrors `partialStrengthenTypedIdJ_sound` with `Ty.oeq` decomposition. -/
theorem partialStrengthenTypedOeqJ_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {baseResult : StrengtheningResult strengthening baseCase}
    {witnessResult : StrengtheningResult strengthening witness}
    (baseSound : StrengtheningSoundness baseResult)
    (witnessSound : StrengtheningSoundness witnessResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOeqJ carrierSuccess leftSuccess rightSuccess
        baseResult witnessResult) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.oeq carrier leftEndpoint rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.oeq targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.oeq =
                  some (Ty.oeq targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedOeqJOfSuccess_sound
            (baseCase := baseCase) (witness := witness)
            (baseTypeStrengthens := baseTypeStrengthens)
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (baseRawStrengthens := baseRawStrengthens)
            (witnessRawStrengthens := witnessRawStrengthens)
            (baseTypeRenames := baseTypeRenames)
            (baseRawRenames := baseRawRenames)
            (witnessRawRenames := witnessRawRenames)
            baseSound.termRenames witnessSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedIdStrictRec`
wrapper.  Same shape as `partialStrengthenTypedIdJ_sound` but with the
strict-identity carrier `Ty.idStrict` plus the `modeIsStrict`
evidence threaded through. -/
theorem partialStrengthenTypedIdStrictRec_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {targetCarrier : Ty level targetScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {targetLeftEndpoint targetRightEndpoint : RawTerm targetScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (carrierSuccess :
      carrier.partialStrengthen? strengthening.back = some targetCarrier)
    (leftSuccess :
      leftEndpoint.partialStrengthen? strengthening.back =
        some targetLeftEndpoint)
    (rightSuccess :
      rightEndpoint.partialStrengthen? strengthening.back =
        some targetRightEndpoint)
    {baseResult : StrengtheningResult strengthening baseCase}
    {witnessResult : StrengtheningResult strengthening witness}
    (baseSound : StrengtheningSoundness baseResult)
    (witnessSound : StrengtheningSoundness witnessResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIdStrictRec modeIsStrict carrierSuccess
        leftSuccess rightSuccess baseResult witnessResult) := by
  cases baseResult with
  | mk targetMotiveType targetBaseRaw targetBaseTerm baseTypeStrengthens
      baseRawStrengthens baseTypeRenames baseRawRenames =>
      cases witnessResult with
      | mk targetWitnessType targetWitnessRaw targetWitnessTerm
          witnessTypeStrengthens witnessRawStrengthens witnessTypeRenames
          witnessRawRenames =>
          have expectedWitnessTypeStrengthens :
              (Ty.idStrict carrier leftEndpoint
                  rightEndpoint).partialStrengthen?
                  strengthening.back =
                some (Ty.idStrict targetCarrier targetLeftEndpoint
                  targetRightEndpoint) := by
            change
              Option.mapThree
                (carrier.partialStrengthen? strengthening.back)
                (leftEndpoint.partialStrengthen? strengthening.back)
                (rightEndpoint.partialStrengthen? strengthening.back)
                Ty.idStrict =
                  some (Ty.idStrict targetCarrier targetLeftEndpoint
                    targetRightEndpoint)
            rw [carrierSuccess, leftSuccess, rightSuccess]
            rfl
          rw [expectedWitnessTypeStrengthens] at witnessTypeStrengthens
          cases witnessTypeStrengthens
          exact partialStrengthenTypedIdStrictRecOfSuccess_sound
            modeIsStrict
            (baseCase := baseCase) (witness := witness)
            (baseTypeStrengthens := baseTypeStrengthens)
            (carrierSuccess := carrierSuccess)
            (leftSuccess := leftSuccess)
            (rightSuccess := rightSuccess)
            (baseRawStrengthens := baseRawStrengthens)
            (witnessRawStrengthens := witnessRawStrengthens)
            (baseTypeRenames := baseTypeRenames)
            (baseRawRenames := baseRawRenames)
            (witnessRawRenames := witnessRawRenames)
            baseSound.termRenames witnessSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEquivApp`
wrapper.  Dual-pivot cascade (`carrierASuccess`/`carrierBSuccess`)
threads through `Ty.equiv` decomposition on the equiv-term child;
the argument child's type aligns via `rw [carrierASuccess]`. -/
theorem partialStrengthenTypedEquivApp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    {equivResult : StrengtheningResult strengthening equivTerm}
    {argumentResult : StrengtheningResult strengthening argumentTerm}
    (equivSound : StrengtheningSoundness equivResult)
    (argumentSound : StrengtheningSoundness argumentResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivApp carrierASuccess carrierBSuccess
        equivResult argumentResult) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      cases equivTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [carrierASuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedEquivAppOfSuccess_sound
            (equivTerm := equivTerm) (argumentTerm := argumentTerm)
            (carrierASuccess := carrierASuccess)
            (carrierBSuccess := carrierBSuccess)
            (equivRawStrengthens := equivRawStrengthens)
            (argumentRawStrengthens := argumentRawStrengthens)
            (equivRawRenames := equivRawRenames)
            (argumentRawRenames := argumentRawRenames)
            equivSound.termRenames argumentSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEquivApply`
wrapper.  Same shape as `partialStrengthenTypedEquivApp_sound` — only
the raw constructor differs (univalence-beta vs the regular equiv
application). -/
theorem partialStrengthenTypedEquivApply_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    {equivResult : StrengtheningResult strengthening equivTerm}
    {argumentResult : StrengtheningResult strengthening argumentTerm}
    (equivSound : StrengtheningSoundness equivResult)
    (argumentSound : StrengtheningSoundness argumentResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivApply carrierASuccess carrierBSuccess
        equivResult argumentResult) := by
  cases equivResult with
  | mk targetEquivType targetEquivRaw targetEquivTerm
      equivTypeStrengthens equivRawStrengthens equivTypeRenames
      equivRawRenames =>
      have expectedEquivTypeStrengthens :
          (Ty.equiv carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.equiv targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.equiv = some (Ty.equiv targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedEquivTypeStrengthens] at equivTypeStrengthens
      cases equivTypeStrengthens
      cases argumentResult with
      | mk targetArgumentType targetArgumentRaw targetArgumentTerm
          argumentTypeStrengthens argumentRawStrengthens
          argumentTypeRenames argumentRawRenames =>
          rw [carrierASuccess] at argumentTypeStrengthens
          cases argumentTypeStrengthens
          exact partialStrengthenTypedEquivApplyOfSuccess_sound
            (equivTerm := equivTerm) (argumentTerm := argumentTerm)
            (carrierASuccess := carrierASuccess)
            (carrierBSuccess := carrierBSuccess)
            (equivRawStrengthens := equivRawStrengthens)
            (argumentRawStrengthens := argumentRawStrengthens)
            (equivRawRenames := equivRawRenames)
            (argumentRawRenames := argumentRawRenames)
            equivSound.termRenames argumentSound.termRenames

/-- Soundness of the App-pattern `partialStrengthenTypedEquivIntroHet`
wrapper.  Closes the heterogeneous-equivalence introduction soundness
chain: dual carrier pivot, four child results (forward + backward
function carriers, plus heterogeneous inverse-law proof functions
whose codomain types are computed by `equivIntroHet*InverseType`).
Mirrors the wrapper's case-cascade and delegates to
`_OfSuccess_sound`. -/
theorem partialStrengthenTypedEquivIntroHet_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back = some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back = some targetCarrierB)
    {forwardResult : StrengtheningResult strengthening forward}
    {backwardResult : StrengtheningResult strengthening backward}
    {leftInvResult : StrengtheningResult strengthening leftInv}
    {rightInvResult : StrengtheningResult strengthening rightInv}
    (forwardSound : StrengtheningSoundness forwardResult)
    (backwardSound : StrengtheningSoundness backwardResult)
    (leftInvSound : StrengtheningSoundness leftInvResult)
    (rightInvSound : StrengtheningSoundness rightInvResult) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivIntroHet carrierASuccess carrierBSuccess
        forwardResult backwardResult leftInvResult rightInvResult) := by
  cases forwardResult with
  | mk targetForwardType targetForwardRaw targetForward
      forwardTypeStrengthens forwardRawStrengthens forwardTypeRenames
      forwardRawRenames =>
      have expectedForwardTypeStrengthens :
          (Ty.arrow carrierA carrierB).partialStrengthen?
              strengthening.back =
            some (Ty.arrow targetCarrierA targetCarrierB) := by
        change
          Option.mapTwo
            (carrierA.partialStrengthen? strengthening.back)
            (carrierB.partialStrengthen? strengthening.back)
            Ty.arrow = some (Ty.arrow targetCarrierA targetCarrierB)
        rw [carrierASuccess, carrierBSuccess]
        rfl
      rw [expectedForwardTypeStrengthens] at forwardTypeStrengthens
      cases forwardTypeStrengthens
      cases backwardResult with
      | mk targetBackwardType targetBackwardRaw targetBackward
          backwardTypeStrengthens backwardRawStrengthens
          backwardTypeRenames backwardRawRenames =>
          have expectedBackwardTypeStrengthens :
              (Ty.arrow carrierB carrierA).partialStrengthen?
                  strengthening.back =
                some (Ty.arrow targetCarrierB targetCarrierA) := by
            change
              Option.mapTwo
                (carrierB.partialStrengthen? strengthening.back)
                (carrierA.partialStrengthen? strengthening.back)
                Ty.arrow = some (Ty.arrow targetCarrierB targetCarrierA)
            rw [carrierBSuccess, carrierASuccess]
            rfl
          rw [expectedBackwardTypeStrengthens] at backwardTypeStrengthens
          cases backwardTypeStrengthens
          have forwardWeakenStrengthens :
              forwardRaw.weaken.partialStrengthen?
                  strengthening.back.lift =
                some targetForwardRaw.weaken := by
            rw [RawTerm.partialStrengthen?_weaken_lift forwardRaw
              strengthening.back, forwardRawStrengthens]
            rfl
          have backwardWeakenStrengthens :
              backwardRaw.weaken.partialStrengthen?
                  strengthening.back.lift =
                some targetBackwardRaw.weaken := by
            rw [RawTerm.partialStrengthen?_weaken_lift backwardRaw
              strengthening.back, backwardRawStrengthens]
            rfl
          have carrierAWeakenStrengthens :
              carrierA.weaken.partialStrengthen?
                  strengthening.back.lift =
                some targetCarrierA.weaken := by
            rw [Ty.partialStrengthen?_weaken_lift carrierA
              strengthening.back, carrierASuccess]
            rfl
          have carrierBWeakenStrengthens :
              carrierB.weaken.partialStrengthen?
                  strengthening.back.lift =
                some targetCarrierB.weaken := by
            rw [Ty.partialStrengthen?_weaken_lift carrierB
              strengthening.back, carrierBSuccess]
            rfl
          have forwardVarAppStrengthens :
              (RawTerm.app forwardRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetForwardRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (forwardRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var
                  ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetForwardRaw.weaken
                    (RawTerm.var
                      ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [forwardWeakenStrengthens]
            rfl
          have backwardVarAppStrengthens :
              (RawTerm.app backwardRaw.weaken
                (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
                ).partialStrengthen? strengthening.back.lift =
                some (RawTerm.app targetBackwardRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)) := by
            change
              Option.mapTwo
                (backwardRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                (some (RawTerm.var
                  ⟨0, Nat.zero_lt_succ targetScope⟩))
                RawTerm.app =
                  some (RawTerm.app targetBackwardRaw.weaken
                    (RawTerm.var
                      ⟨0, Nat.zero_lt_succ targetScope⟩))
            rw [backwardWeakenStrengthens]
            rfl
          have leftNestedAppStrengthens :
              (RawTerm.app backwardRaw.weaken
                (RawTerm.app forwardRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
                ).partialStrengthen? strengthening.back.lift =
                some
                  (RawTerm.app targetBackwardRaw.weaken
                    (RawTerm.app targetForwardRaw.weaken
                      (RawTerm.var
                        ⟨0, Nat.zero_lt_succ targetScope⟩))) := by
            change
              Option.mapTwo
                (backwardRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                ((RawTerm.app forwardRaw.weaken
                  (RawTerm.var
                    ⟨0, Nat.zero_lt_succ sourceScope⟩)
                  ).partialStrengthen? strengthening.back.lift)
                RawTerm.app =
                  some
                    (RawTerm.app targetBackwardRaw.weaken
                      (RawTerm.app targetForwardRaw.weaken
                        (RawTerm.var
                          ⟨0, Nat.zero_lt_succ targetScope⟩)))
            rw [backwardWeakenStrengthens, forwardVarAppStrengthens]
            rfl
          have rightNestedAppStrengthens :
              (RawTerm.app forwardRaw.weaken
                (RawTerm.app backwardRaw.weaken
                  (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
                ).partialStrengthen? strengthening.back.lift =
                some
                  (RawTerm.app targetForwardRaw.weaken
                    (RawTerm.app targetBackwardRaw.weaken
                      (RawTerm.var
                        ⟨0, Nat.zero_lt_succ targetScope⟩))) := by
            change
              Option.mapTwo
                (forwardRaw.weaken.partialStrengthen?
                  strengthening.back.lift)
                ((RawTerm.app backwardRaw.weaken
                  (RawTerm.var
                    ⟨0, Nat.zero_lt_succ sourceScope⟩)
                  ).partialStrengthen? strengthening.back.lift)
                RawTerm.app =
                  some
                    (RawTerm.app targetForwardRaw.weaken
                      (RawTerm.app targetBackwardRaw.weaken
                        (RawTerm.var
                          ⟨0, Nat.zero_lt_succ targetScope⟩)))
            rw [forwardWeakenStrengthens, backwardVarAppStrengthens]
            rfl
          have leftInverseTypeStrengthens :
              (equivIntroHetLeftInverseType carrierA forwardRaw
                  backwardRaw).partialStrengthen?
                  strengthening.back =
                some (equivIntroHetLeftInverseType targetCarrierA
                  targetForwardRaw targetBackwardRaw) := by
            have leftCodomainStrengthens :
                (equivIntroHetLeftInverseCodomain carrierA
                    forwardRaw backwardRaw).partialStrengthen?
                    strengthening.back.lift =
                  some
                    (equivIntroHetLeftInverseCodomain targetCarrierA
                      targetForwardRaw targetBackwardRaw) := by
              change
                Option.mapThree
                  (carrierA.weaken.partialStrengthen?
                    strengthening.back.lift)
                  ((RawTerm.app backwardRaw.weaken
                    (RawTerm.app forwardRaw.weaken
                      (RawTerm.var
                        ⟨0, Nat.zero_lt_succ sourceScope⟩))
                    ).partialStrengthen? strengthening.back.lift)
                  (some (RawTerm.var
                    ⟨0, Nat.zero_lt_succ targetScope⟩))
                  Ty.id =
                    some
                      (equivIntroHetLeftInverseCodomain
                        targetCarrierA targetForwardRaw
                        targetBackwardRaw)
              rw [carrierAWeakenStrengthens,
                leftNestedAppStrengthens]
              rfl
            change
              Option.mapTwo
                (carrierA.partialStrengthen? strengthening.back)
                ((equivIntroHetLeftInverseCodomain carrierA
                  forwardRaw backwardRaw).partialStrengthen?
                  strengthening.back.lift)
                Ty.piTy =
                  some (equivIntroHetLeftInverseType targetCarrierA
                    targetForwardRaw targetBackwardRaw)
            rw [carrierASuccess, leftCodomainStrengthens]
            rfl
          have rightInverseTypeStrengthens :
              (equivIntroHetRightInverseType carrierB forwardRaw
                  backwardRaw).partialStrengthen?
                  strengthening.back =
                some (equivIntroHetRightInverseType targetCarrierB
                  targetForwardRaw targetBackwardRaw) := by
            have rightCodomainStrengthens :
                (equivIntroHetRightInverseCodomain carrierB
                    forwardRaw backwardRaw).partialStrengthen?
                    strengthening.back.lift =
                  some
                    (equivIntroHetRightInverseCodomain targetCarrierB
                      targetForwardRaw targetBackwardRaw) := by
              change
                Option.mapThree
                  (carrierB.weaken.partialStrengthen?
                    strengthening.back.lift)
                  ((RawTerm.app forwardRaw.weaken
                    (RawTerm.app backwardRaw.weaken
                      (RawTerm.var
                        ⟨0, Nat.zero_lt_succ sourceScope⟩))
                    ).partialStrengthen? strengthening.back.lift)
                  (some (RawTerm.var
                    ⟨0, Nat.zero_lt_succ targetScope⟩))
                  Ty.id =
                    some
                      (equivIntroHetRightInverseCodomain
                        targetCarrierB targetForwardRaw
                        targetBackwardRaw)
              rw [carrierBWeakenStrengthens,
                rightNestedAppStrengthens]
              rfl
            change
              Option.mapTwo
                (carrierB.partialStrengthen? strengthening.back)
                ((equivIntroHetRightInverseCodomain carrierB
                  forwardRaw backwardRaw).partialStrengthen?
                  strengthening.back.lift)
                Ty.piTy =
                  some (equivIntroHetRightInverseType targetCarrierB
                    targetForwardRaw targetBackwardRaw)
            rw [carrierBSuccess, rightCodomainStrengthens]
            rfl
          cases leftInvResult with
          | mk targetLeftInvType targetLeftInvRaw targetLeftInv
              leftInvTypeStrengthens leftInvRawStrengthens
              leftInvTypeRenames leftInvRawRenames =>
              rw [leftInverseTypeStrengthens] at leftInvTypeStrengthens
              cases leftInvTypeStrengthens
              cases rightInvResult with
              | mk targetRightInvType targetRightInvRaw
                  targetRightInv rightInvTypeStrengthens
                  rightInvRawStrengthens rightInvTypeRenames
                  rightInvRawRenames =>
                  rw [rightInverseTypeStrengthens] at rightInvTypeStrengthens
                  cases rightInvTypeStrengthens
                  exact partialStrengthenTypedEquivIntroHetOfSuccess_sound
                    (forward := forward) (backward := backward)
                    (leftInv := leftInv) (rightInv := rightInv)
                    (carrierASuccess := carrierASuccess)
                    (carrierBSuccess := carrierBSuccess)
                    (forwardRawStrengthens := forwardRawStrengthens)
                    (backwardRawStrengthens := backwardRawStrengthens)
                    (forwardRawRenames := forwardRawRenames)
                    (backwardRawRenames := backwardRawRenames)
                    (leftInvRawRenames := leftInvRawRenames)
                    (rightInvRawRenames := rightInvRawRenames)
                    forwardSound.termRenames backwardSound.termRenames
                    leftInvSound.termRenames rightInvSound.termRenames

/-! ## Dispatcher-level soundness — leaf prologue.

The `partialStrengthenTyped?` top-level dispatcher (78 arms) takes any
typed term to an optional `StrengtheningResult`.  Wrapper-level
soundness already certifies each successful arm: every leaf and every
recursive wrapper has a `_sound` theorem promoting its
`StrengtheningResult` into a `StrengtheningSoundness` certificate.

This prologue lifts the wrapper certificates to the dispatcher for the
closed-leaf cases (var, unit, boolean/nat zero literals, interval
endpoints).  Each such theorem inverts the dispatcher's arm by
unfolding the auxiliary `match` plus, for `var`, the option-cases on
`strengthening.back`, then immediately applies the matching wrapper
soundness.

Cumulatively, these lemmas plus the wrapper soundness theorems form
the foundation for the headline image theorem trio (right-inverse,
totality, iff): once every dispatcher arm is lifted, the trio becomes
a uniform consequence of structural recursion on `Term`.  This commit
ships the cheap, no-subterm-recursion fragment so the recursive arms
can build on a known-good prologue. -/

/-- Dispatcher soundness at the `Term.var` arm.  After refactoring the
dispatcher's var body to term-mode `match h :`, the standard `split`
machinery penetrates the resulting `Option` match and exposes a clean
witness `survives : strengthening.back sourcePosition = some targetPosition`
that feeds the wrapper soundness directly. -/
theorem partialStrengthenTyped?_atVar_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (sourcePosition : Fin sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.var (context := sourceCtx) sourcePosition))
    (success : partialStrengthenTyped?
        (Term.var (context := sourceCtx) sourcePosition) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetPosition survives
    cases success
    exact partialStrengthenTypedVarOfSurvives_sound strengthening sourcePosition
      targetPosition survives

/-- Dispatcher soundness at the `Term.natSucc` arm.  First arm with a
recursive `partialStrengthenTyped?` sub-call: the inductive hypothesis
on the predecessor flows through as an explicit `predecessorIH`
parameter, which `split at success` plus `cases success` reduces to
exactly the wrapper soundness premise.  Same term-mode `match h :`
refactor as `atVar`: standard equation lemmas, no Option.casesOn
motive trap. -/
theorem partialStrengthenTyped?_atNatSucc_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {predecessorRaw : RawTerm sourceScope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (predecessorIH : ∀ predecessorResult,
        partialStrengthenTyped? predecessor strengthening =
            some predecessorResult →
          StrengtheningSoundness predecessorResult)
    (result : StrengtheningResult strengthening
      (Term.natSucc (predecessor := predecessor)))
    (success : partialStrengthenTyped?
        (Term.natSucc (predecessor := predecessor)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i predecessorResult predecessorRecurse
    cases success
    exact partialStrengthenTypedNatSucc_sound
      (predecessorSound := predecessorIH predecessorResult predecessorRecurse)

/-- Dispatcher soundness at the `Term.optionSome` arm.  Single-recurse
arm with no type-shape strengthening: identical proof shape to
`atNatSucc`. -/
theorem partialStrengthenTyped?_atOptionSome_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (valueIH : ∀ valueResult,
        partialStrengthenTyped? valueTerm strengthening =
            some valueResult →
          StrengtheningSoundness valueResult)
    (result : StrengtheningResult strengthening
      (Term.optionSome (valueTerm := valueTerm)))
    (success : partialStrengthenTyped?
        (Term.optionSome (valueTerm := valueTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i valueResult valueRecurse
    cases success
    exact partialStrengthenTypedOptionSome_sound
      (valueSound := valueIH valueResult valueRecurse)

/-- Dispatcher soundness at the `Term.modIntro` arm. -/
theorem partialStrengthenTyped?_atModIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerTerm strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.modIntro (innerTerm := innerTerm)))
    (success : partialStrengthenTyped?
        (Term.modIntro (innerTerm := innerTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedModIntro_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.modElim` arm. -/
theorem partialStrengthenTyped?_atModElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerTerm strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.modElim (innerTerm := innerTerm)))
    (success : partialStrengthenTyped?
        (Term.modElim (innerTerm := innerTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedModElim_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.subsume` arm. -/
theorem partialStrengthenTyped?_atSubsume_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerTerm strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.subsume (innerTerm := innerTerm)))
    (success : partialStrengthenTyped?
        (Term.subsume (innerTerm := innerTerm)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedSubsume_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.intervalOpp` arm. -/
theorem partialStrengthenTyped?_atIntervalOpp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerRaw : RawTerm sourceScope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (innerIH : ∀ innerResult,
        partialStrengthenTyped? innerValue strengthening =
            some innerResult →
          StrengtheningSoundness innerResult)
    (result : StrengtheningResult strengthening
      (Term.intervalOpp (innerValue := innerValue)))
    (success : partialStrengthenTyped?
        (Term.intervalOpp (innerValue := innerValue)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i innerResult innerRecurse
    cases success
    exact partialStrengthenTypedIntervalOpp_sound
      (innerSound := innerIH innerResult innerRecurse)

/-- Dispatcher soundness at the `Term.intervalMeet` arm.  Binary
recurse on two interval subterms, no type-shape strengthening: two
inductive hypotheses (one per subterm) thread to the wrapper. -/
theorem partialStrengthenTyped?_atIntervalMeet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (leftIH : ∀ leftResult,
        partialStrengthenTyped? leftValue strengthening =
            some leftResult →
          StrengtheningSoundness leftResult)
    (rightIH : ∀ rightResult,
        partialStrengthenTyped? rightValue strengthening =
            some rightResult →
          StrengtheningSoundness rightResult)
    (result : StrengtheningResult strengthening
      (Term.intervalMeet (leftValue := leftValue) (rightValue := rightValue)))
    (success : partialStrengthenTyped?
        (Term.intervalMeet (leftValue := leftValue) (rightValue := rightValue))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i leftResult leftRecurse
    split at success
    · cases success
    · rename_i rightResult rightRecurse
      cases success
      exact partialStrengthenTypedIntervalMeet_sound
        (leftSound := leftIH leftResult leftRecurse)
        (rightSound := rightIH rightResult rightRecurse)

/-- Dispatcher soundness at the `Term.intervalJoin` arm.  Mirrors
`atIntervalMeet`. -/
theorem partialStrengthenTyped?_atIntervalJoin_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (leftIH : ∀ leftResult,
        partialStrengthenTyped? leftValue strengthening =
            some leftResult →
          StrengtheningSoundness leftResult)
    (rightIH : ∀ rightResult,
        partialStrengthenTyped? rightValue strengthening =
            some rightResult →
          StrengtheningSoundness rightResult)
    (result : StrengtheningResult strengthening
      (Term.intervalJoin (leftValue := leftValue) (rightValue := rightValue)))
    (success : partialStrengthenTyped?
        (Term.intervalJoin (leftValue := leftValue) (rightValue := rightValue))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i leftResult leftRecurse
    split at success
    · cases success
    · rename_i rightResult rightRecurse
      cases success
      exact partialStrengthenTypedIntervalJoin_sound
        (leftSound := leftIH leftResult leftRecurse)
        (rightSound := rightIH rightResult rightRecurse)

/-- Dispatcher soundness at the `Term.listCons` arm.  Binary recurse
on head and tail subterms; the elementType strengthening is implicit
in the wrapper's type-equality discharge. -/
theorem partialStrengthenTyped?_atListCons_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (headIH : ∀ headResult,
        partialStrengthenTyped? headTerm strengthening =
            some headResult →
          StrengtheningSoundness headResult)
    (tailIH : ∀ tailResult,
        partialStrengthenTyped? tailTerm strengthening =
            some tailResult →
          StrengtheningSoundness tailResult)
    (result : StrengtheningResult strengthening
      (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm)))
    (success : partialStrengthenTyped?
        (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i headResult headRecurse
    split at success
    · cases success
    · rename_i tailResult tailRecurse
      cases success
      exact partialStrengthenTypedListCons_sound
        (headSound := headIH headResult headRecurse)
        (tailSound := tailIH tailResult tailRecurse)

/-- Dispatcher soundness at the `Term.listNil` arm.  Type-only
strengthening (no value recurse): the dispatcher branches solely on
`elementType.partialStrengthen?`, and the wrapper soundness consumes
the witness directly. -/
theorem partialStrengthenTyped?_atListNil_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (elementType : Ty level sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.listNil (context := sourceCtx) (elementType := elementType)))
    (success : partialStrengthenTyped?
        (Term.listNil (context := sourceCtx) (elementType := elementType))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    cases success
    exact partialStrengthenTypedListNilOfType_sound strengthening
      elementType targetElementType elementSuccess

/-- Dispatcher soundness at the `Term.optionNone` arm.  Mirrors
`atListNil`: type-only strengthening, wrapper applied directly. -/
theorem partialStrengthenTyped?_atOptionNone_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (elementType : Ty level sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.optionNone (context := sourceCtx) (elementType := elementType)))
    (success : partialStrengthenTyped?
        (Term.optionNone (context := sourceCtx) (elementType := elementType))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    cases success
    exact partialStrengthenTypedOptionNoneOfType_sound strengthening
      elementType targetElementType elementSuccess

/-- Dispatcher soundness at the `Term.eitherInl` arm.  Mixed shape:
right-type strengthening witness + single value-subterm IH. -/
theorem partialStrengthenTyped?_atEitherInl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (valueIH : ∀ valueResult,
        partialStrengthenTyped? valueTerm strengthening =
            some valueResult →
          StrengtheningSoundness valueResult)
    (result : StrengtheningResult strengthening
      (Term.eitherInl (rightType := rightType) (valueTerm := valueTerm)))
    (success : partialStrengthenTyped?
        (Term.eitherInl (rightType := rightType) (valueTerm := valueTerm))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetRightType rightSuccess
    split at success
    · cases success
    · rename_i valueResult valueRecurse
      cases success
      exact partialStrengthenTypedEitherInlOfRightType_sound
        rightSuccess (valueSound := valueIH valueResult valueRecurse)

/-- Dispatcher soundness at the `Term.eitherInr` arm.  Mirrors
`atEitherInl` with left-type strengthening on the unused side. -/
theorem partialStrengthenTyped?_atEitherInr_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (valueIH : ∀ valueResult,
        partialStrengthenTyped? valueTerm strengthening =
            some valueResult →
          StrengtheningSoundness valueResult)
    (result : StrengtheningResult strengthening
      (Term.eitherInr (leftType := leftType) (valueTerm := valueTerm)))
    (success : partialStrengthenTyped?
        (Term.eitherInr (leftType := leftType) (valueTerm := valueTerm))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftType leftSuccess
    split at success
    · cases success
    · rename_i valueResult valueRecurse
      cases success
      exact partialStrengthenTypedEitherInrOfLeftType_sound
        leftSuccess (valueSound := valueIH valueResult valueRecurse)

/-- Dispatcher soundness at the `Term.oeqFunext` arm.  Function-
extensionality intro: two type witnesses (domain + codomain) plus
two raw witnesses (leftFunctionRaw + rightFunctionRaw) plus one
flat-context value IH (pointwiseProof). -/
theorem partialStrengthenTyped?_atOeqFunext_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {leftFunctionRaw rightFunctionRaw : RawTerm sourceScope}
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pointwiseIH : ∀ pointwiseResult,
        partialStrengthenTyped? pointwiseProof strengthening =
            some pointwiseResult →
          StrengtheningSoundness pointwiseResult)
    (result : StrengtheningResult strengthening
      (Term.oeqFunext (domainType := domainType)
        (codomainType := codomainType)
        (leftFunctionRaw := leftFunctionRaw)
        (rightFunctionRaw := rightFunctionRaw)
        pointwiseProof))
    (success : partialStrengthenTyped?
        (Term.oeqFunext (domainType := domainType)
          (codomainType := codomainType)
          (leftFunctionRaw := leftFunctionRaw)
          (rightFunctionRaw := rightFunctionRaw)
          pointwiseProof) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i targetLeftFunctionRaw leftSuccess
        split at success
        · cases success
        · rename_i targetRightFunctionRaw rightSuccess
          split at success
          · cases success
          · rename_i pointwiseResult pointwiseRecurse
            cases success
            exact partialStrengthenTypedOeqFunext_sound
              domainType codomainType targetDomainType targetCodomainType
              leftFunctionRaw rightFunctionRaw targetLeftFunctionRaw
              targetRightFunctionRaw domainSuccess codomainSuccess
              leftSuccess rightSuccess
              (pointwiseIH pointwiseResult pointwiseRecurse)

/-- Dispatcher soundness at the `Term.idStrictRefl` arm.  Strict-mode
identity reflexivity: one type witness (carrier) + one raw witness,
no value IH, plus the `modeIsStrict` discipline witness. -/
theorem partialStrengthenTyped?_atIdStrictRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.idStrictRefl (context := sourceCtx)
        (carrier := carrier) modeIsStrict rawWitness))
    (success : partialStrengthenTyped?
        (Term.idStrictRefl (context := sourceCtx)
          (carrier := carrier) modeIsStrict rawWitness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetWitness witnessSuccess
      cases success
      exact partialStrengthenTypedIdStrictRefl_sound modeIsStrict
        carrierSuccess witnessSuccess

/-- Dispatcher soundness at the `Term.idStrictRec` arm.  Strict-mode
J-eliminator: one type witness (carrier) + two raw witnesses
(leftEndpoint + rightEndpoint) + two flat-context value IHs
(baseCase + witness), plus `modeIsStrict`. -/
theorem partialStrengthenTyped?_atIdStrictRec_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseCase strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (witnessIH : ∀ witnessResult,
        partialStrengthenTyped? witness strengthening =
            some witnessResult →
          StrengtheningSoundness witnessResult)
    (result : StrengtheningResult strengthening
      (Term.idStrictRec (motiveType := motiveType) modeIsStrict
        baseCase witness))
    (success : partialStrengthenTyped?
        (Term.idStrictRec (motiveType := motiveType) modeIsStrict
          baseCase witness) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i baseResult baseRecurse
          split at success
          · cases success
          · rename_i witnessResult witnessRecurse
            cases success
            exact partialStrengthenTypedIdStrictRec_sound modeIsStrict
              carrierSuccess leftSuccess rightSuccess
              (baseIH baseResult baseRecurse)
              (witnessIH witnessResult witnessRecurse)

/-- Dispatcher soundness at the `Term.pathApp` arm.  Cubical path
application: three type witnesses (carrierType + leftEndpoint +
rightEndpoint as Ty.path components) + two flat-context value IHs
(pathTerm + intervalTerm), plus `modeIsUnivalent`. -/
theorem partialStrengthenTyped?_atPathApp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pathIH : ∀ pathResult,
        partialStrengthenTyped? pathTerm strengthening =
            some pathResult →
          StrengtheningSoundness pathResult)
    (intervalIH : ∀ intervalResult,
        partialStrengthenTyped? intervalTerm strengthening =
            some intervalResult →
          StrengtheningSoundness intervalResult)
    (result : StrengtheningResult strengthening
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm))
    (success : partialStrengthenTyped?
        (Term.pathApp modeIsUnivalent pathTerm intervalTerm)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierType carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i pathResult pathRecurse
          split at success
          · cases success
          · rename_i intervalResult intervalRecurse
            cases success
            exact partialStrengthenTypedPathApp_sound modeIsUnivalent
              carrierSuccess leftSuccess rightSuccess
              (pathIH pathResult pathRecurse)
              (intervalIH intervalResult intervalRecurse)

/-- Dispatcher soundness at the `Term.glueElim` arm.  Cubical glue
elimination: one type witness (baseType) + one raw witness
(boundaryWitness) + one flat-context value IH (gluedValue), plus
`modeIsUnivalent`. -/
theorem partialStrengthenTyped?_atGlueElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {gluedValue :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (gluedIH : ∀ gluedResult,
        partialStrengthenTyped? gluedValue strengthening =
            some gluedResult →
          StrengtheningSoundness gluedResult)
    (result : StrengtheningResult strengthening
      (Term.glueElim modeIsUnivalent gluedValue))
    (success : partialStrengthenTyped?
        (Term.glueElim modeIsUnivalent gluedValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetBaseType baseSuccess
    split at success
    · cases success
    · rename_i targetBoundaryWitness boundarySuccess
      split at success
      · cases success
      · rename_i gluedResult gluedRecurse
        cases success
        exact partialStrengthenTypedGlueElim_sound modeIsUnivalent
          baseSuccess boundarySuccess (gluedIH gluedResult gluedRecurse)

/-- Dispatcher soundness at the `Term.codataUnfold` arm.  Codata
introduction: one raw witness on `outputType` (state type rides
through the transition arrow's type strengthening) + two
flat-context value IHs (`initialState` + `transition`). -/
theorem partialStrengthenTyped?_atCodataUnfold_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (stateIH : ∀ stateResult,
        partialStrengthenTyped? initialState strengthening =
            some stateResult →
          StrengtheningSoundness stateResult)
    (transitionIH : ∀ transitionResult,
        partialStrengthenTyped? transition strengthening =
            some transitionResult →
          StrengtheningSoundness transitionResult)
    (result : StrengtheningResult strengthening
      (Term.codataUnfold initialState transition))
    (success : partialStrengthenTyped?
        (Term.codataUnfold initialState transition) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetOutputType outputSuccess
    split at success
    · cases success
    · rename_i stateResult stateRecurse
      split at success
      · cases success
      · rename_i transitionResult transitionRecurse
        cases success
        exact partialStrengthenTypedCodataUnfold_sound outputSuccess
          (stateSound := stateIH stateResult stateRecurse)
          (transitionSound := transitionIH transitionResult transitionRecurse)

/-- Dispatcher soundness at the `Term.codataDest` arm.  Codata
destruction: two type witnesses (`stateType` + `outputType`, both at
`strengthening.back`) + one flat-context value IH on `codataValue`. -/
theorem partialStrengthenTyped?_atCodataDest_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (codataIH : ∀ codataResult,
        partialStrengthenTyped? codataValue strengthening =
            some codataResult →
          StrengtheningSoundness codataResult)
    (result : StrengtheningResult strengthening
      (Term.codataDest codataValue))
    (success : partialStrengthenTyped?
        (Term.codataDest codataValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetStateType stateSuccess
    split at success
    · cases success
    · rename_i targetOutputType outputSuccess
      split at success
      · cases success
      · rename_i codataResult codataRecurse
        cases success
        exact partialStrengthenTypedCodataDest_sound stateSuccess
          outputSuccess
          (codataSound := codataIH codataResult codataRecurse)

/-- Dispatcher soundness at the `Term.sessionSend` arm.  Session-send:
one raw witness on the protocol step (lifted to
`strengthening.back` since the protocol step lives at flat scope) +
two flat-context value IHs (`channel` + `payload`). -/
theorem partialStrengthenTyped?_atSessionSend_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (channelIH : ∀ channelResult,
        partialStrengthenTyped? channel strengthening =
            some channelResult →
          StrengtheningSoundness channelResult)
    (payloadIH : ∀ payloadResult,
        partialStrengthenTyped? payload strengthening =
            some payloadResult →
          StrengtheningSoundness payloadResult)
    (result : StrengtheningResult strengthening
      (Term.sessionSend protocolStep channel payload))
    (success : partialStrengthenTyped?
        (Term.sessionSend protocolStep channel payload) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetProtocolStep protocolSuccess
    split at success
    · cases success
    · rename_i channelResult channelRecurse
      split at success
      · cases success
      · rename_i payloadResult payloadRecurse
        cases success
        exact partialStrengthenTypedSessionSend_sound protocolSuccess
          (channelSound := channelIH channelResult channelRecurse)
          (payloadSound := payloadIH payloadResult payloadRecurse)

/-- Dispatcher soundness at the `Term.sessionRecv` arm.  Session-recv:
one raw witness on the protocol step + one flat-context value IH on
`channel`. -/
theorem partialStrengthenTyped?_atSessionRecv_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (channelIH : ∀ channelResult,
        partialStrengthenTyped? channel strengthening =
            some channelResult →
          StrengtheningSoundness channelResult)
    (result : StrengtheningResult strengthening
      (Term.sessionRecv channel))
    (success : partialStrengthenTyped?
        (Term.sessionRecv channel) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetProtocolStep protocolSuccess
    split at success
    · cases success
    · rename_i channelResult channelRecurse
      cases success
      exact partialStrengthenTypedSessionRecv_sound protocolSuccess
        (channelSound := channelIH channelResult channelRecurse)

/-- Dispatcher soundness at the `Term.equivReflId` arm.  Closed-leaf
equivalence-reflexivity-at-id: one type witness on `carrier`, NO
value IH.  The wrapper takes `carrier` and `targetCarrier` as
positional explicit arguments; the dispatcher leaf grabs the latter
from `split`'s rename. -/
theorem partialStrengthenTyped?_atEquivReflId_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.equivReflId (context := sourceCtx) (carrier := carrier)))
    (success : partialStrengthenTyped?
        (Term.equivReflId (context := sourceCtx) (carrier := carrier))
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    cases success
    exact partialStrengthenTypedEquivReflId_sound carrier targetCarrier
      carrierSuccess

/-- Dispatcher soundness at the `Term.recordIntro` arm.  Single-field
record introduction: no raw or type witnesses (`Ty.record` is built
from the strengthened field type via `congrArg`), one flat-context
value IH (`firstField`). -/
theorem partialStrengthenTyped?_atRecordIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    {firstField : Term sourceCtx singleFieldType firstRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (fieldIH : ∀ fieldResult,
        partialStrengthenTyped? firstField strengthening =
            some fieldResult →
          StrengtheningSoundness fieldResult)
    (result : StrengtheningResult strengthening
      (Term.recordIntro (firstField := firstField)))
    (success : partialStrengthenTyped?
        (Term.recordIntro (firstField := firstField)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i fieldResult fieldRecurse
    cases success
    exact partialStrengthenTypedRecordIntro_sound
      (fieldSound := fieldIH fieldResult fieldRecurse)

/-- Dispatcher soundness at the `Term.recordProj` arm.  Record
projection: one type witness (`singleFieldType` at
`strengthening.back`) + one flat-context value IH (`recordValue`). -/
theorem partialStrengthenTyped?_atRecordProj_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    {recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (recordIH : ∀ recordResult,
        partialStrengthenTyped? recordValue strengthening =
            some recordResult →
          StrengtheningSoundness recordResult)
    (result : StrengtheningResult strengthening
      (Term.recordProj (recordValue := recordValue)))
    (success : partialStrengthenTyped?
        (Term.recordProj (recordValue := recordValue)) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFieldType fieldSuccess
    split at success
    · cases success
    · rename_i recordResult recordRecurse
      cases success
      exact partialStrengthenTypedRecordProj_sound fieldSuccess
        (recordSound := recordIH recordResult recordRecurse)

/-- Dispatcher soundness at the `Term.refineIntro` arm.  Refinement
introduction: one raw witness on the predicate (lifted to
`strengthening.back.lift` since the predicate binds the refined
variable) + two flat-context value IHs (`baseValue` carrying the
underlying datum + `predicateProof` discharging the refinement). -/
theorem partialStrengthenTyped?_atRefineIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRaw proofRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseValue strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (proofIH : ∀ proofResult,
        partialStrengthenTyped? predicateProof strengthening =
            some proofResult →
          StrengtheningSoundness proofResult)
    (result : StrengtheningResult strengthening
      (Term.refineIntro predicate baseValue predicateProof))
    (success : partialStrengthenTyped?
        (Term.refineIntro predicate baseValue predicateProof)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetPredicate predicateSuccess
    split at success
    · cases success
    · rename_i baseResult baseRecurse
      split at success
      · cases success
      · rename_i proofResult proofRecurse
        cases success
        exact partialStrengthenTypedRefineIntro_sound predicateSuccess
          (baseSound := baseIH baseResult baseRecurse)
          (proofSound := proofIH proofResult proofRecurse)

/-- Dispatcher soundness at the `Term.refineElim` arm.  Refinement
elimination: one type witness (`baseType` at `strengthening.back`) +
one raw witness on the predicate (lifted) + one flat-context value
IH (`refinedValue`). -/
theorem partialStrengthenTyped?_atRefineElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (refinedIH : ∀ refinedResult,
        partialStrengthenTyped? refinedValue strengthening =
            some refinedResult →
          StrengtheningSoundness refinedResult)
    (result : StrengtheningResult strengthening
      (Term.refineElim refinedValue))
    (success : partialStrengthenTyped?
        (Term.refineElim refinedValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetBaseType baseSuccess
    split at success
    · cases success
    · rename_i targetPredicate predicateSuccess
      split at success
      · cases success
      · rename_i refinedResult refinedRecurse
        cases success
        exact partialStrengthenTypedRefineElim_sound baseSuccess
          predicateSuccess
          (refinedSound := refinedIH refinedResult refinedRecurse)

/-- Dispatcher soundness at the `Term.cumulUp` arm.  Universe-level
cumulation: no raw or type witnesses (all level data
`lowerLevel`/`higherLevel`/`cumulMonotone`/`levelLeLow`/`levelLeHigh`
forwards through as positional data into the wrapper), one
flat-context value IH (`typeCode`). -/
theorem partialStrengthenTyped?_atCumulUp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (codeIH : ∀ codeResult,
        partialStrengthenTyped? typeCode strengthening =
            some codeResult →
          StrengtheningSoundness codeResult)
    (result : StrengtheningResult strengthening
      (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
        levelLeHigh typeCode))
    (success : partialStrengthenTyped?
        (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
          levelLeHigh typeCode) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i codeResult codeRecurse
    cases success
    exact partialStrengthenTypedCumulUp_sound lowerLevel higherLevel
      cumulMonotone levelLeLow levelLeHigh
      (codeSound := codeIH codeResult codeRecurse)

/-- Dispatcher soundness at the `Term.eitherMatch` arm.  ι-eliminator
with three type witnesses (leftType + rightType + motiveType, all at
`strengthening.back`) plus three flat-context value IHs
(scrutinee + leftBranch + rightBranch). -/
theorem partialStrengthenTyped?_atEitherMatch_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (leftIH : ∀ leftResult,
        partialStrengthenTyped? leftBranch strengthening =
            some leftResult →
          StrengtheningSoundness leftResult)
    (rightIH : ∀ rightResult,
        partialStrengthenTyped? rightBranch strengthening =
            some rightResult →
          StrengtheningSoundness rightResult)
    (result : StrengtheningResult strengthening
      (Term.eitherMatch (motiveType := motiveType) scrutinee leftBranch
        rightBranch))
    (success : partialStrengthenTyped?
        (Term.eitherMatch (motiveType := motiveType) scrutinee leftBranch
          rightBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftType leftSuccess
    split at success
    · cases success
    · rename_i targetRightType rightSuccess
      split at success
      · cases success
      · rename_i targetMotiveType motiveSuccess
        split at success
        · cases success
        · rename_i scrutineeResult scrutineeRecurse
          split at success
          · cases success
          · rename_i leftResult leftRecurse
            split at success
            · cases success
            · rename_i rightResult rightRecurse
              cases success
              exact partialStrengthenTypedEitherMatch_sound
                leftSuccess rightSuccess motiveSuccess
                (scrutineeIH scrutineeResult scrutineeRecurse)
                (leftIH leftResult leftRecurse)
                (rightIH rightResult rightRecurse)

/-- Dispatcher soundness at the `Term.refl` arm.  HoTT identity
introduction: one type witness (carrier) plus one raw witness
(rawWitness) — no value IH at all. -/
theorem partialStrengthenTyped?_atRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.refl (context := sourceCtx) (carrier := carrier) rawWitness))
    (success : partialStrengthenTyped?
        (Term.refl (context := sourceCtx) (carrier := carrier) rawWitness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetWitness witnessSuccess
      cases success
      exact partialStrengthenTypedRefl_sound carrierSuccess witnessSuccess

/-- Dispatcher soundness at the `Term.oeqRefl` arm.  Mirrors `atRefl`
for observational equality: one type witness + one raw witness, no
value IH. -/
theorem partialStrengthenTyped?_atOeqRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {rawWitness : RawTerm sourceScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.oeqRefl (context := sourceCtx) (carrier := carrier)
        rawWitness))
    (success : partialStrengthenTyped?
        (Term.oeqRefl (context := sourceCtx) (carrier := carrier)
          rawWitness) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetWitness witnessSuccess
      cases success
      exact partialStrengthenTypedOeqRefl_sound carrierSuccess
        witnessSuccess

/-- Dispatcher soundness at the `Term.idJ` arm.  HoTT J-eliminator:
one type witness (carrier) + two raw witnesses (leftEndpoint +
rightEndpoint) + two flat-context value IHs (baseCase + witness). -/
theorem partialStrengthenTyped?_atIdJ_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseCase strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (witnessIH : ∀ witnessResult,
        partialStrengthenTyped? witness strengthening =
            some witnessResult →
          StrengtheningSoundness witnessResult)
    (result : StrengtheningResult strengthening
      (Term.idJ (motiveType := motiveType) baseCase witness))
    (success : partialStrengthenTyped?
        (Term.idJ (motiveType := motiveType) baseCase witness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i baseResult baseRecurse
          split at success
          · cases success
          · rename_i witnessResult witnessRecurse
            cases success
            exact partialStrengthenTypedIdJ_sound
              carrierSuccess leftSuccess rightSuccess
              (baseIH baseResult baseRecurse)
              (witnessIH witnessResult witnessRecurse)

/-- Dispatcher soundness at the `Term.oeqJ` arm.  Mirrors `atIdJ` for
observational equality: one type witness + two raw witnesses + two
flat-context value IHs. -/
theorem partialStrengthenTyped?_atOeqJ_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseCase strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (witnessIH : ∀ witnessResult,
        partialStrengthenTyped? witness strengthening =
            some witnessResult →
          StrengtheningSoundness witnessResult)
    (result : StrengtheningResult strengthening
      (Term.oeqJ (motiveType := motiveType) baseCase witness))
    (success : partialStrengthenTyped?
        (Term.oeqJ (motiveType := motiveType) baseCase witness)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i baseResult baseRecurse
          split at success
          · cases success
          · rename_i witnessResult witnessRecurse
            cases success
            exact partialStrengthenTypedOeqJ_sound
              carrierSuccess leftSuccess rightSuccess
              (baseIH baseResult baseRecurse)
              (witnessIH witnessResult witnessRecurse)

/-- Dispatcher soundness at the `Term.boolElim` arm.  ι-eliminator
shape: one binder-type strengthening witness on the motive slot
(`strengthening.back.lift`) plus three flat-context value IHs
(scrutinee + then + else). -/
theorem partialStrengthenTyped?_atBoolElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (thenIH : ∀ thenResult,
        partialStrengthenTyped? thenBranch strengthening =
            some thenResult →
          StrengtheningSoundness thenResult)
    (elseIH : ∀ elseResult,
        partialStrengthenTyped? elseBranch strengthening =
            some elseResult →
          StrengtheningSoundness elseResult)
    (result : StrengtheningResult strengthening
      (Term.boolElim (motiveType := motiveType) scrutinee thenBranch
        elseBranch))
    (success : partialStrengthenTyped?
        (Term.boolElim (motiveType := motiveType) scrutinee thenBranch
          elseBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetMotiveType motiveSuccess
    split at success
    · cases success
    · rename_i scrutineeResult scrutineeRecurse
      split at success
      · cases success
      · rename_i thenResult thenRecurse
        split at success
        · cases success
        · rename_i elseResult elseRecurse
          cases success
          exact partialStrengthenTypedBoolElim_sound motiveSuccess
            (scrutineeIH scrutineeResult scrutineeRecurse)
            (thenIH thenResult thenRecurse)
            (elseIH elseResult elseRecurse)

/-- Dispatcher soundness at the `Term.natElim` arm.  ι-eliminator with
non-dependent motive at the kernel level: no type witness needed,
three flat-context value IHs (scrutinee + zero + succ). -/
theorem partialStrengthenTyped?_atNatElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (zeroIH : ∀ zeroResult,
        partialStrengthenTyped? zeroBranch strengthening =
            some zeroResult →
          StrengtheningSoundness zeroResult)
    (succIH : ∀ succResult,
        partialStrengthenTyped? succBranch strengthening =
            some succResult →
          StrengtheningSoundness succResult)
    (result : StrengtheningResult strengthening
      (Term.natElim (motiveType := motiveType) scrutinee zeroBranch
        succBranch))
    (success : partialStrengthenTyped?
        (Term.natElim (motiveType := motiveType) scrutinee zeroBranch
          succBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i scrutineeResult scrutineeRecurse
    split at success
    · cases success
    · rename_i zeroResult zeroRecurse
      split at success
      · cases success
      · rename_i succResult succRecurse
        cases success
        exact partialStrengthenTypedNatElim_sound
          (scrutineeIH scrutineeResult scrutineeRecurse)
          (zeroIH zeroResult zeroRecurse)
          (succIH succResult succRecurse)

/-- Dispatcher soundness at the `Term.natRec` arm.  Mirrors `atNatElim`
shape: no type witness, three flat-context value IHs (scrutinee +
zero + succ); succ branch has the recursor's higher-kinded arrow. -/
theorem partialStrengthenTyped?_atNatRec_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (zeroIH : ∀ zeroResult,
        partialStrengthenTyped? zeroBranch strengthening =
            some zeroResult →
          StrengtheningSoundness zeroResult)
    (succIH : ∀ succResult,
        partialStrengthenTyped? succBranch strengthening =
            some succResult →
          StrengtheningSoundness succResult)
    (result : StrengtheningResult strengthening
      (Term.natRec (motiveType := motiveType) scrutinee zeroBranch
        succBranch))
    (success : partialStrengthenTyped?
        (Term.natRec (motiveType := motiveType) scrutinee zeroBranch
          succBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i scrutineeResult scrutineeRecurse
    split at success
    · cases success
    · rename_i zeroResult zeroRecurse
      split at success
      · cases success
      · rename_i succResult succRecurse
        cases success
        exact partialStrengthenTypedNatRec_sound
          (scrutineeIH scrutineeResult scrutineeRecurse)
          (zeroIH zeroResult zeroRecurse)
          (succIH succResult succRecurse)

/-- Dispatcher soundness at the `Term.listElim` arm.  Parametric ι-
eliminator: one type witness (element type at `strengthening.back`)
plus three flat-context value IHs (scrutinee + nil + cons). -/
theorem partialStrengthenTyped?_atListElim_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (nilIH : ∀ nilResult,
        partialStrengthenTyped? nilBranch strengthening =
            some nilResult →
          StrengtheningSoundness nilResult)
    (consIH : ∀ consResult,
        partialStrengthenTyped? consBranch strengthening =
            some consResult →
          StrengtheningSoundness consResult)
    (result : StrengtheningResult strengthening
      (Term.listElim (motiveType := motiveType) scrutinee nilBranch
        consBranch))
    (success : partialStrengthenTyped?
        (Term.listElim (motiveType := motiveType) scrutinee nilBranch
          consBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    split at success
    · cases success
    · rename_i scrutineeResult scrutineeRecurse
      split at success
      · cases success
      · rename_i nilResult nilRecurse
        split at success
        · cases success
        · rename_i consResult consRecurse
          cases success
          exact partialStrengthenTypedListElim_sound elementSuccess
            (scrutineeIH scrutineeResult scrutineeRecurse)
            (nilIH nilResult nilRecurse)
            (consIH consResult consRecurse)

/-- Dispatcher soundness at the `Term.optionMatch` arm.  Mirrors
`atListElim`: one element-type witness + three flat-context value IHs
(scrutinee + none + some). -/
theorem partialStrengthenTyped?_atOptionMatch_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (scrutineeIH : ∀ scrutineeResult,
        partialStrengthenTyped? scrutinee strengthening =
            some scrutineeResult →
          StrengtheningSoundness scrutineeResult)
    (noneIH : ∀ noneResult,
        partialStrengthenTyped? noneBranch strengthening =
            some noneResult →
          StrengtheningSoundness noneResult)
    (someIH : ∀ someResult,
        partialStrengthenTyped? someBranch strengthening =
            some someResult →
          StrengtheningSoundness someResult)
    (result : StrengtheningResult strengthening
      (Term.optionMatch (motiveType := motiveType) scrutinee noneBranch
        someBranch))
    (success : partialStrengthenTyped?
        (Term.optionMatch (motiveType := motiveType) scrutinee noneBranch
          someBranch) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementType elementSuccess
    split at success
    · cases success
    · rename_i scrutineeResult scrutineeRecurse
      split at success
      · cases success
      · rename_i noneResult noneRecurse
        split at success
        · cases success
        · rename_i someResult someRecurse
          cases success
          exact partialStrengthenTypedOptionMatch_sound elementSuccess
            (scrutineeIH scrutineeResult scrutineeRecurse)
            (noneIH noneResult noneRecurse)
            (someIH someResult someRecurse)

/-- Dispatcher soundness at the `Term.app` arm.  Non-dependent
application: two type strengthening witnesses (domain + codomain,
both at `strengthening.back` since the codomain in `Ty.arrow` does
not see the bound variable) plus two value IHs (function + argument). -/
theorem partialStrengthenTyped?_atApp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (functionIH : ∀ functionResult,
        partialStrengthenTyped? functionTerm strengthening =
            some functionResult →
          StrengtheningSoundness functionResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.app (codomainType := codomainType)
        functionTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.app (codomainType := codomainType)
          functionTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i functionResult functionRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedApp_sound
            domainSuccess codomainSuccess
            (functionIH functionResult functionRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.appPi` arm.  Dependent application:
domain strengthens at `strengthening.back`, codomain strengthens under
the binder via `strengthening.back.lift`; two value IHs. -/
theorem partialStrengthenTyped?_atAppPi_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (functionIH : ∀ functionResult,
        partialStrengthenTyped? functionTerm strengthening =
            some functionResult →
          StrengtheningSoundness functionResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.appPi (codomainType := codomainType)
        functionTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.appPi (codomainType := codomainType)
          functionTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i functionResult functionRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedAppPi_sound
            domainSuccess codomainSuccess
            (functionIH functionResult functionRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.pair` arm.  Sigma-pair shape:
one binder-type strengthening witness on the second-type slot, plus
two value-subterm IHs (first value at `firstType`, second value at
the substituted type). -/
theorem partialStrengthenTyped?_atPair_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (firstIH : ∀ firstResult,
        partialStrengthenTyped? firstValue strengthening =
            some firstResult →
          StrengtheningSoundness firstResult)
    (secondIH : ∀ secondResult,
        partialStrengthenTyped? secondValue strengthening =
            some secondResult →
          StrengtheningSoundness secondResult)
    (result : StrengtheningResult strengthening
      (Term.pair (secondType := secondType) firstValue secondValue))
    (success : partialStrengthenTyped?
        (Term.pair (secondType := secondType) firstValue secondValue)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetSecondType secondTypeSuccess
    split at success
    · cases success
    · rename_i firstResult firstRecurse
      split at success
      · cases success
      · rename_i secondResult secondRecurse
        cases success
        exact partialStrengthenTypedPair_sound secondTypeSuccess
          (firstIH firstResult firstRecurse)
          (secondIH secondResult secondRecurse)

/-- Dispatcher soundness at the `Term.fst` arm.  Sigma first-projection:
two type strengthening witnesses (firstType + secondType) plus a
single sigma-value IH. -/
theorem partialStrengthenTyped?_atFst_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pairIH : ∀ pairResult,
        partialStrengthenTyped? pairTerm strengthening =
            some pairResult →
          StrengtheningSoundness pairResult)
    (result : StrengtheningResult strengthening (Term.fst pairTerm))
    (success :
      partialStrengthenTyped? (Term.fst pairTerm) strengthening =
        some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFirstType firstSuccess
    split at success
    · cases success
    · rename_i targetSecondType secondSuccess
      split at success
      · cases success
      · rename_i pairResult pairRecurse
        cases success
        exact partialStrengthenTypedFst_sound firstSuccess secondSuccess
          (pairIH pairResult pairRecurse)

/-- Dispatcher soundness at the `Term.snd` arm.  Mirrors `atFst` —
two type strengthening witnesses plus a single sigma-value IH. -/
theorem partialStrengthenTyped?_atSnd_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pairIH : ∀ pairResult,
        partialStrengthenTyped? pairTerm strengthening =
            some pairResult →
          StrengtheningSoundness pairResult)
    (result : StrengtheningResult strengthening (Term.snd pairTerm))
    (success :
      partialStrengthenTyped? (Term.snd pairTerm) strengthening =
        some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFirstType firstSuccess
    split at success
    · cases success
    · rename_i targetSecondType secondSuccess
      split at success
      · cases success
      · rename_i pairResult pairRecurse
        cases success
        exact partialStrengthenTypedSnd_sound firstSuccess secondSuccess
          (pairIH pairResult pairRecurse)

/-- Dispatcher soundness at the `Term.unit` arm.  Closed-leaf: the
dispatcher returns `some (partialStrengthenTypedUnit strengthening)`
unconditionally, so the soundness is the wrapper soundness applied
directly. -/
theorem partialStrengthenTyped?_atUnit_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening (Term.unit (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.unit (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedUnit_sound strengthening

/-- Dispatcher soundness at the `Term.boolTrue` arm. -/
theorem partialStrengthenTyped?_atBoolTrue_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.boolTrue (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.boolTrue (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedBoolTrue_sound strengthening

/-- Dispatcher soundness at the `Term.boolFalse` arm. -/
theorem partialStrengthenTyped?_atBoolFalse_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.boolFalse (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.boolFalse (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedBoolFalse_sound strengthening

/-- Dispatcher soundness at the `Term.natZero` arm. -/
theorem partialStrengthenTyped?_atNatZero_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.natZero (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.natZero (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedNatZero_sound strengthening

/-- Dispatcher soundness at the `Term.interval0` arm. -/
theorem partialStrengthenTyped?_atInterval0_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.interval0 (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.interval0 (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedInterval0_sound strengthening

/-- Dispatcher soundness at the `Term.interval1` arm. -/
theorem partialStrengthenTyped?_atInterval1_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.interval1 (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.interval1 (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedInterval1_sound strengthening

/-- Dispatcher soundness at the `Term.arrowCode` arm.  Type-code closed
leaf with two flat-scope raw witnesses (domain + codomain) plus the
universe-level positional forwarding (`outerLevel`/`levelLe`).  No
value IH — the wrapper consumes the raw witnesses directly. -/
theorem partialStrengthenTyped?_atArrowCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.arrowCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw))
    (success : partialStrengthenTyped?
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainCodeRaw domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainCodeRaw codomainSuccess
      cases success
      exact partialStrengthenTypedArrowCode_sound outerLevel levelLe
        domainCodeRaw codomainCodeRaw targetDomainCodeRaw
        targetCodomainCodeRaw domainSuccess codomainSuccess

/-- Dispatcher soundness at the `Term.piTyCode` arm.  Π-type-code closed
leaf with one flat-scope raw (`domainCodeRaw`) plus one lifted raw
(`codomainCodeRaw` at `scope + 1`).  The codomain rides
`strengthening.back.lift` to track the bound variable from the Π
binder.  Universe-level positional forwarding identical to arrow. -/
theorem partialStrengthenTyped?_atPiTyCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.piTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw))
    (success : partialStrengthenTyped?
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainCodeRaw domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainCodeRaw codomainSuccess
      cases success
      exact partialStrengthenTypedPiTyCode_sound outerLevel levelLe
        domainCodeRaw codomainCodeRaw targetDomainCodeRaw
        targetCodomainCodeRaw domainSuccess codomainSuccess

/-- Dispatcher soundness at the `Term.sigmaTyCode` arm.  Σ-type-code
closed leaf, structurally identical to piTyCode: one flat raw
(`domainCodeRaw`) plus one lifted raw (`codomainCodeRaw` at
`scope + 1`, dependent on the first component). -/
theorem partialStrengthenTyped?_atSigmaTyCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw))
    (success : partialStrengthenTyped?
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainCodeRaw domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainCodeRaw codomainSuccess
      cases success
      exact partialStrengthenTypedSigmaTyCode_sound outerLevel levelLe
        domainCodeRaw codomainCodeRaw targetDomainCodeRaw
        targetCodomainCodeRaw domainSuccess codomainSuccess

/-- Dispatcher soundness at the `Term.productCode` arm.  Non-dependent
pair type-code closed leaf with two flat-scope raw witnesses (first +
second components, both at `sourceScope`).  Universe-level positional
forwarding identical to arrow. -/
theorem partialStrengthenTyped?_atProductCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.productCode (context := sourceCtx) outerLevel levelLe
        firstCodeRaw secondCodeRaw))
    (success : partialStrengthenTyped?
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRaw secondCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFirstCodeRaw firstSuccess
    split at success
    · cases success
    · rename_i targetSecondCodeRaw secondSuccess
      cases success
      exact partialStrengthenTypedProductCode_sound outerLevel levelLe
        firstCodeRaw secondCodeRaw targetFirstCodeRaw
        targetSecondCodeRaw firstSuccess secondSuccess

/-- Dispatcher soundness at the `Term.sumCode` arm.  Binary sum
type-code closed leaf with two flat-scope raw witnesses (left + right
summands).  Structurally identical to productCode. -/
theorem partialStrengthenTyped?_atSumCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.sumCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw))
    (success : partialStrengthenTyped?
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftCodeRaw leftSuccess
    split at success
    · cases success
    · rename_i targetRightCodeRaw rightSuccess
      cases success
      exact partialStrengthenTypedSumCode_sound outerLevel levelLe
        leftCodeRaw rightCodeRaw targetLeftCodeRaw
        targetRightCodeRaw leftSuccess rightSuccess

/-- Dispatcher soundness at the `Term.listCode` arm.  List-type-code
closed leaf with a single flat-scope raw witness (`elementCodeRaw`)
plus the universe-level positional forwarding (`outerLevel`/
`levelLe`).  No value IH; the wrapper consumes the raw witness
directly. -/
theorem partialStrengthenTyped?_atListCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.listCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw))
    (success : partialStrengthenTyped?
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementCodeRaw elementSuccess
    cases success
    exact partialStrengthenTypedListCode_sound outerLevel levelLe
      elementCodeRaw targetElementCodeRaw elementSuccess

/-- Dispatcher soundness at the `Term.optionCode` arm.  Option-type-code
closed leaf with a single flat-scope raw witness (`elementCodeRaw`).
Structurally identical to `listCode`. -/
theorem partialStrengthenTyped?_atOptionCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.optionCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw))
    (success : partialStrengthenTyped?
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementCodeRaw elementSuccess
    cases success
    exact partialStrengthenTypedOptionCode_sound outerLevel levelLe
      elementCodeRaw targetElementCodeRaw elementSuccess

/-- Dispatcher soundness at the `Term.eitherCode` arm.  Either-type-code
closed leaf with two flat-scope raw witnesses (left + right summand
codes).  Universe-level positional forwarding identical to arrow. -/
theorem partialStrengthenTyped?_atEitherCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.eitherCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw))
    (success : partialStrengthenTyped?
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftCodeRaw leftSuccess
    split at success
    · cases success
    · rename_i targetRightCodeRaw rightSuccess
      cases success
      exact partialStrengthenTypedEitherCode_sound outerLevel levelLe
        leftCodeRaw rightCodeRaw targetLeftCodeRaw
        targetRightCodeRaw leftSuccess rightSuccess

/-- Dispatcher soundness at the `Term.idCode` arm.  Identity-type-code
closed leaf with THREE flat-scope raw witnesses (typeCode + left
endpoint + right endpoint).  Three nested `split at success` calls
plus three sequential `rename_i` to peel each Option layer. -/
theorem partialStrengthenTyped?_atIdCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.idCode (context := sourceCtx) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw))
    (success : partialStrengthenTyped?
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRaw leftRaw rightRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetTypeCodeRaw typeSuccess
    split at success
    · cases success
    · rename_i targetLeftRaw leftSuccess
      split at success
      · cases success
      · rename_i targetRightRaw rightSuccess
        cases success
        exact partialStrengthenTypedIdCode_sound outerLevel levelLe
          typeCodeRaw leftRaw rightRaw targetTypeCodeRaw
          targetLeftRaw targetRightRaw typeSuccess leftSuccess
          rightSuccess

/-- Dispatcher soundness at the `Term.equivCode` arm.  Equivalence-
type-code closed leaf with two flat-scope raw witnesses
(`leftTypeCodeRaw` + `rightTypeCodeRaw`).  Structurally identical to
`eitherCode`. -/
theorem partialStrengthenTyped?_atEquivCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.equivCode (context := sourceCtx) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw))
    (success : partialStrengthenTyped?
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRaw rightTypeCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftTypeCodeRaw leftSuccess
    split at success
    · cases success
    · rename_i targetRightTypeCodeRaw rightSuccess
      cases success
      exact partialStrengthenTypedEquivCode_sound outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw targetLeftTypeCodeRaw
        targetRightTypeCodeRaw leftSuccess rightSuccess

/-- Dispatcher soundness at the `Term.universeCode` arm.  The bare-
universe-of-codes producer carries no scope-dependent payload; the
dispatcher returns the wrapper unconditionally and the leaf simply
`cases success` and applies the wrapper's `_sound` companion. -/
theorem partialStrengthenTyped?_atUniverseCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.universeCode (context := sourceCtx) innerLevel outerLevel
        cumulOk levelLe))
    (success : partialStrengthenTyped?
        (Term.universeCode (context := sourceCtx) innerLevel outerLevel
          cumulOk levelLe) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedUniverseCode_sound strengthening
    innerLevel outerLevel cumulOk levelLe

/-- Dispatcher soundness at the `Term.funextRefl` arm.  Closed-leaf
canonical funext reflexivity: two flat type witnesses (`domainType`
and `codomainType`) plus one lifted raw witness (`applyRaw` at
`scope + 1`).  No value IH. -/
theorem partialStrengthenTyped?_atFunextRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.funextRefl (context := sourceCtx) domainType codomainType
        applyRaw))
    (success : partialStrengthenTyped?
        (Term.funextRefl (context := sourceCtx) domainType codomainType
          applyRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i targetApplyRaw applySuccess
        cases success
        exact partialStrengthenTypedFunextRefl_sound domainType
          codomainType targetDomainType targetCodomainType applyRaw
          targetApplyRaw domainSuccess codomainSuccess applySuccess

/-- Dispatcher soundness at the `Term.equivReflIdAtId` arm.  Closed-
leaf equivalence-reflexivity at the identity type: one positional
universe-level pair (`innerLevel`/`innerLevelLt`) + one type witness
(`carrier`) + one flat-scope raw witness (`carrierRaw`).  No value
IH. -/
theorem partialStrengthenTyped?_atEquivReflIdAtId_imp_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel
        innerLevelLt carrier carrierRaw))
    (success : partialStrengthenTyped?
        (Term.equivReflIdAtId (context := sourceCtx) innerLevel
          innerLevelLt carrier carrierRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetCarrierRaw carrierRawSuccess
      cases success
      exact partialStrengthenTypedEquivReflIdAtId_sound innerLevel
        innerLevelLt carrier targetCarrier carrierRaw targetCarrierRaw
        carrierSuccess carrierRawSuccess

/-- Dispatcher soundness at the `Term.funextReflAtId` arm.
Structurally identical to `funextRefl` — two flat type witnesses plus
one lifted raw witness; only the wrapper's resulting type differs
(Id-typed instead of canonical funext form). -/
theorem partialStrengthenTyped?_atFunextReflAtId_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.funextReflAtId (context := sourceCtx) domainType
        codomainType applyRaw))
    (success : partialStrengthenTyped?
        (Term.funextReflAtId (context := sourceCtx) domainType
          codomainType applyRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i targetApplyRaw applySuccess
        cases success
        exact partialStrengthenTypedFunextReflAtId_sound domainType
          codomainType targetDomainType targetCodomainType applyRaw
          targetApplyRaw domainSuccess codomainSuccess applySuccess

/-- Dispatcher soundness at the `Term.equivApp` arm.  Heterogeneous-carrier
equivalence application: both carrier types strengthen flat (no binder
shift) and the two value children supply IHs via the standard pattern. -/
theorem partialStrengthenTyped?_atEquivApp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivIH : ∀ equivResult,
        partialStrengthenTyped? equivTerm strengthening =
            some equivResult →
          StrengtheningSoundness equivResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.equivApp equivTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.equivApp equivTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierASuccess
    split at success
    · cases success
    · rename_i targetCarrierB carrierBSuccess
      split at success
      · cases success
      · rename_i equivResult equivRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedEquivApp_sound
            carrierASuccess carrierBSuccess
            (equivIH equivResult equivRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.equivApply` arm.  Univalence-flavoured
equivalence application: same shape as the `equivApp` arm — both carrier
types strengthen flat, two value children supply IHs.  Only the raw
constructor differs (`RawTerm.equivApply` vs `RawTerm.equivApp`). -/
theorem partialStrengthenTyped?_atEquivApply_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivIH : ∀ equivResult,
        partialStrengthenTyped? equivTerm strengthening =
            some equivResult →
          StrengtheningSoundness equivResult)
    (argumentIH : ∀ argumentResult,
        partialStrengthenTyped? argumentTerm strengthening =
            some argumentResult →
          StrengtheningSoundness argumentResult)
    (result : StrengtheningResult strengthening
      (Term.equivApply equivTerm argumentTerm))
    (success : partialStrengthenTyped?
        (Term.equivApply equivTerm argumentTerm) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierASuccess
    split at success
    · cases success
    · rename_i targetCarrierB carrierBSuccess
      split at success
      · cases success
      · rename_i equivResult equivRecurse
        split at success
        · cases success
        · rename_i argumentResult argumentRecurse
          cases success
          exact partialStrengthenTypedEquivApply_sound
            carrierASuccess carrierBSuccess
            (equivIH equivResult equivRecurse)
            (argumentIH argumentResult argumentRecurse)

/-- Dispatcher soundness at the `Term.uaToEquiv` arm.  Univalence-β extractor:
two flat type witnesses (`leftTy`/`rightTy`), two flat raw witnesses
(`leftTyRaw`/`rightTyRaw`), and one value IH on the universe-path proof.
Universe-level positional forwarding (`innerLevel`/`innerLevelLt`) rides
through the wrapper. -/
theorem partialStrengthenTyped?_atUaToEquiv_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (proofIH : ∀ proofResult,
        partialStrengthenTyped? proof strengthening =
            some proofResult →
          StrengtheningSoundness proofResult)
    (result : StrengtheningResult strengthening
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof))
    (success : partialStrengthenTyped?
        (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
          leftTy rightTy leftTyRaw rightTyRaw proof) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftTy leftTyStrengthens
    split at success
    · cases success
    · rename_i targetRightTy rightTyStrengthens
      split at success
      · cases success
      · rename_i targetLeftTyRaw leftRawStrengthens
        split at success
        · cases success
        · rename_i targetRightTyRaw rightRawStrengthens
          split at success
          · cases success
          · rename_i proofResult proofRecurse
            cases success
            exact partialStrengthenTypedUaToEquiv_sound innerLevel
              innerLevelLt leftTy rightTy targetLeftTy targetRightTy
              leftTyRaw rightTyRaw targetLeftTyRaw targetRightTyRaw
              leftTyStrengthens rightTyStrengthens leftRawStrengthens
              rightRawStrengthens (proofIH proofResult proofRecurse)

/-- Dispatcher soundness at the `Term.equivIntroHet` arm.
Heterogeneous-carrier equivalence introduction: two carrier types plus
four function-shaped IHs (forward, backward, left-inverse, right-inverse).
Six sequential splits feed the wrapper soundness with all four IH
witnesses. -/
theorem partialStrengthenTyped?_atEquivIntroHet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (forwardIH : ∀ forwardResult,
        partialStrengthenTyped? forward strengthening =
            some forwardResult →
          StrengtheningSoundness forwardResult)
    (backwardIH : ∀ backwardResult,
        partialStrengthenTyped? backward strengthening =
            some backwardResult →
          StrengtheningSoundness backwardResult)
    (leftInvIH : ∀ leftInvResult,
        partialStrengthenTyped? leftInv strengthening =
            some leftInvResult →
          StrengtheningSoundness leftInvResult)
    (rightInvIH : ∀ rightInvResult,
        partialStrengthenTyped? rightInv strengthening =
            some rightInvResult →
          StrengtheningSoundness rightInvResult)
    (result : StrengtheningResult strengthening
      (Term.equivIntroHet forward backward leftInv rightInv))
    (success : partialStrengthenTyped?
        (Term.equivIntroHet forward backward leftInv rightInv)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierASuccess
    split at success
    · cases success
    · rename_i targetCarrierB carrierBSuccess
      split at success
      · cases success
      · rename_i forwardResult forwardRecurse
        split at success
        · cases success
        · rename_i backwardResult backwardRecurse
          split at success
          · cases success
          · rename_i leftInvResult leftInvRecurse
            split at success
            · cases success
            · rename_i rightInvResult rightInvRecurse
              cases success
              exact partialStrengthenTypedEquivIntroHet_sound
                carrierASuccess carrierBSuccess
                (forwardIH forwardResult forwardRecurse)
                (backwardIH backwardResult backwardRecurse)
                (leftInvIH leftInvResult leftInvRecurse)
                (rightInvIH rightInvResult rightInvRecurse)

/-- Dispatcher soundness at the `Term.uaIntroHet` arm.  Heterogeneous
univalence introduction: positional `innerLevel`/`innerLevelLt`, two
carrier-type witnesses, four raw witnesses (`carrierARaw`, `carrierBRaw`,
`forwardRaw`, `backwardRaw`), and a single equivalence-witness value
IH. -/
theorem partialStrengthenTyped?_atUaIntroHet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (equivIH : ∀ equivResult,
        partialStrengthenTyped? equivWitness strengthening =
            some equivResult →
          StrengtheningSoundness equivResult)
    (result : StrengtheningResult strengthening
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness))
    (success : partialStrengthenTyped?
        (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
          carrierARaw carrierBRaw equivWitness) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierA carrierAStrengthens
    split at success
    · cases success
    · rename_i targetCarrierB carrierBStrengthens
      split at success
      · cases success
      · rename_i targetCarrierARaw carrierARawStrengthens
        split at success
        · cases success
        · rename_i targetCarrierBRaw carrierBRawStrengthens
          split at success
          · cases success
          · rename_i targetForwardRaw forwardRawStrengthens
            split at success
            · cases success
            · rename_i targetBackwardRaw backwardRawStrengthens
              split at success
              · cases success
              · rename_i equivResult equivRecurse
                cases success
                exact partialStrengthenTypedUaIntroHet_sound innerLevel
                  innerLevelLt targetCarrierA targetCarrierB
                  carrierARaw carrierBRaw targetCarrierARaw targetCarrierBRaw
                  targetForwardRaw targetBackwardRaw
                  carrierAStrengthens carrierBStrengthens
                  carrierARawStrengthens carrierBRawStrengthens
                  forwardRawStrengthens backwardRawStrengthens
                  (equivIH equivResult equivRecurse)

/-- Dispatcher soundness at the `Term.funextIntroHet` arm.
Heterogeneous-carrier funext introduction.  Closed leaf: two type
witnesses (`domainType`/`codomainType`) and two lifted raw witnesses
(`applyARaw`/`applyBRaw` under the binder via `strengthening.back.lift`).
No value IH — the wrapper consumes the raw witnesses directly. -/
theorem partialStrengthenTyped?_atFunextIntroHet_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.funextIntroHet (context := sourceCtx) domainType codomainType
        applyARaw applyBRaw))
    (success : partialStrengthenTyped?
        (Term.funextIntroHet (context := sourceCtx) domainType codomainType
          applyARaw applyBRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainStrengthens
    split at success
    · cases success
    · rename_i targetCodomainType codomainStrengthens
      split at success
      · cases success
      · rename_i targetApplyARaw applyAStrengthens
        split at success
        · cases success
        · rename_i targetApplyBRaw applyBStrengthens
          cases success
          exact partialStrengthenTypedFunextIntroHet_sound domainType
            codomainType targetDomainType targetCodomainType applyARaw
            applyBRaw targetApplyARaw targetApplyBRaw
            domainStrengthens codomainStrengthens
            applyAStrengthens applyBStrengthens

/-- Dispatcher soundness at the `Term.effectPerform` arm.  The arm
threads three Ty witnesses (effect-tag raw, argument carrier, result
carrier) plus two value-level recursive results (operation tag,
arguments).  The `canPerformOperation` predicate is mode/effect-row
metadata that passes through unstrengthened.  The leaf derives the
`effectTagRenames` rename-direction fact from `effectTagSuccess` via
`RawTerm.partialStrengthen?_imp_rename`, then delegates to
`partialStrengthenTypedEffectPerform_sound`. -/
theorem partialStrengthenTyped?_atEffectPerform_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {effectTag : RawTerm sourceScope}
    {effectRow : Effects.EffectRow}
    {operationSignature :
      Effects.OperationSignature (Ty level sourceScope)}
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (operationIH : ∀ operationResult,
        partialStrengthenTyped? operationTag strengthening =
            some operationResult →
          StrengtheningSoundness operationResult)
    (argumentsIH : ∀ argumentsResult,
        partialStrengthenTyped? arguments strengthening =
            some argumentsResult →
          StrengtheningSoundness argumentsResult)
    (result : StrengtheningResult strengthening
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments))
    (success : partialStrengthenTyped?
        (Term.effectPerform (context := sourceCtx) effectTag effectRow
          operationSignature canPerformOperation operationTag arguments)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetEffectTag effectTagSuccess
    split at success
    · cases success
    · rename_i targetArgumentCarrier argumentCarrierSuccess
      split at success
      · cases success
      · rename_i targetResultCarrier resultCarrierSuccess
        split at success
        · cases success
        · rename_i operationResult operationRecurse
          split at success
          · cases success
          · rename_i argumentsResult argumentsRecurse
            cases success
            have effectTagRenames :
                effectTag = targetEffectTag.rename strengthening.forward :=
              RawTerm.partialStrengthen?_imp_rename effectTag
                strengthening.forward strengthening.back
                strengthening.injectsBack targetEffectTag effectTagSuccess
            exact partialStrengthenTypedEffectPerform_sound
              effectTag targetEffectTag effectRow operationSignature
              targetArgumentCarrier targetResultCarrier
              canPerformOperation effectTagSuccess
              argumentCarrierSuccess resultCarrierSuccess
              (operationIH operationResult operationRecurse)
              (argumentsIH argumentsResult argumentsRecurse)
              effectTagRenames

/-- Dispatcher soundness at the `Term.glueIntro` arm.  Carries one Ty
witness (baseType), one raw witness (boundaryWitness) under the
cubical mode-univalent flag, plus two value-level IHs (baseValue,
partialValue).  Both value children share the same baseType — partial
glue is the boundary half of the cubical glue type.  Delegates to
`partialStrengthenTypedGlueIntro_sound` which derives both rename
directions internally. -/
theorem partialStrengthenTyped?_atGlueIntro_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (baseIH : ∀ baseResult,
        partialStrengthenTyped? baseValue strengthening =
            some baseResult →
          StrengtheningSoundness baseResult)
    (partialIH : ∀ partialResult,
        partialStrengthenTyped? partialValue strengthening =
            some partialResult →
          StrengtheningSoundness partialResult)
    (result : StrengtheningResult strengthening
      (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
        boundaryWitness baseValue partialValue))
    (success : partialStrengthenTyped?
        (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
          boundaryWitness baseValue partialValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetBaseType baseTypeSuccess
    split at success
    · cases success
    · rename_i targetBoundaryWitness boundarySuccess
      split at success
      · cases success
      · rename_i baseResult baseRecurse
        split at success
        · cases success
        · rename_i partialResult partialRecurse
          cases success
          exact partialStrengthenTypedGlueIntro_sound
            modeIsUnivalent baseType targetBaseType
            boundaryWitness targetBoundaryWitness
            baseTypeSuccess boundarySuccess
            (baseIH baseResult baseRecurse)
            (partialIH partialResult partialRecurse)

/-- Dispatcher soundness at the `Term.pathLam` arm.  Path-lambda is the
first under-binder cubical leaf: the body lives in a context extended
by `Ty.interval`, so the body IH ranges over
`strengthening.lift Ty.interval Ty.interval rfl` strengthening (the
binder shift preserves the interval-typed slot).  Carries 1 Ty
witness (carrier) + 2 raw witnesses (left/right endpoints) +
1 body IH; the wrapper derives all rename directions internally. -/
theorem partialStrengthenTyped?_atPathLam_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (bodyIH : ∀ bodyResult,
        partialStrengthenTyped? body
            (strengthening.lift Ty.interval Ty.interval rfl) =
            some bodyResult →
          StrengtheningSoundness bodyResult)
    (result : StrengtheningResult strengthening
      (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body))
    (success : partialStrengthenTyped?
        (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
          leftEndpoint rightEndpoint body) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierType carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i bodyResult bodyRecurse
          cases success
          exact partialStrengthenTypedPathLam_sound
            modeIsUnivalent carrierSuccess leftSuccess rightSuccess
            (bodyIH bodyResult bodyRecurse)

/-- Dispatcher soundness at the `Term.lam` arm.  Lam is the first
under-binder leaf whose binder type is itself strengthening-mediated:
the body lives in `sourceCtx.cons domainType`, the strengthened body
must live in `targetCtx.cons targetDomainType`, and the lift uses the
witness `domainSuccess` as a typeclass-style cargo.  The body IH is
therefore quantified over the pair `(targetDomainType, domainSuccess)`
rather than a fixed target — first dispatcher leaf with this shape;
applies again to `lamPi` and any future binder whose argument type is
not closed.  Two Ty witnesses (domain, codomain) thread through; the
wrapper derives both rename directions internally. -/
theorem partialStrengthenTyped?_atLam_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (bodyIH : ∀ targetDomainType
        (domainSuccess :
          domainType.partialStrengthen? strengthening.back =
            some targetDomainType)
        bodyResult,
        partialStrengthenTyped? body
            (strengthening.lift domainType targetDomainType
              domainSuccess) =
            some bodyResult →
          StrengtheningSoundness bodyResult)
    (result : StrengtheningResult strengthening
      (Term.lam (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body))
    (success : partialStrengthenTyped?
        (Term.lam (context := sourceCtx) (domainType := domainType)
          (codomainType := codomainType) body) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i _ codomainSuccess
      split at success
      · cases success
      · rename_i bodyResult bodyRecurse
        cases success
        exact partialStrengthenTypedLam_sound
          domainSuccess codomainSuccess
          (bodyIH targetDomainType domainSuccess bodyResult
            bodyRecurse)

/-- Dispatcher soundness at the `Term.lamPi` arm.  Dependent-Π lambda
mirrors `lam`'s dependent-lift body-IH shape, but the codomain lives
in `Ty level (sourceScope + 1)` (inside the binder), so no codomain
witness threads through the dispatcher — `partialStrengthenTypedLamPi`
takes only `domainSuccess` and the body result carries the codomain
strengthen-evidence in its `StrengtheningResult`.  Body IH is
quantified over `(targetDomainType, domainSuccess)` because the body
recursion's strengthening (`strengthening.lift domainType
targetDomainType domainSuccess`) depends on the witness. -/
theorem partialStrengthenTyped?_atLamPi_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (bodyIH : ∀ targetDomainType
        (domainSuccess :
          domainType.partialStrengthen? strengthening.back =
            some targetDomainType)
        bodyResult,
        partialStrengthenTyped? body
            (strengthening.lift domainType targetDomainType
              domainSuccess) =
            some bodyResult →
          StrengtheningSoundness bodyResult)
    (result : StrengtheningResult strengthening
      (Term.lamPi (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body))
    (success : partialStrengthenTyped?
        (Term.lamPi (context := sourceCtx) (domainType := domainType)
          (codomainType := codomainType) body) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i bodyResult bodyRecurse
      cases success
      exact partialStrengthenTypedLamPi_sound
        domainSuccess
        (bodyIH targetDomainType domainSuccess bodyResult
          bodyRecurse)

/-- Dispatcher soundness at the `Term.hcomp` arm.  Cubical homogeneous
composition over a closed-form carrier: both `sidesValue` and
`capValue` live at the same `carrierType`, so the dispatcher carries
no explicit Ty/raw witnesses — the wrapper aligns `capResult`'s
carrier-type strengthening against `sidesResult`'s internally via
`rw [carrierStrengthens] at capTypeStrengthens`.  Mirrors the
two-child-IH shape of glueIntro but without the boundary/witness
threading. -/
theorem partialStrengthenTyped?_atHcomp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sidesIH : ∀ sidesResult,
        partialStrengthenTyped? sidesValue strengthening =
            some sidesResult →
          StrengtheningSoundness sidesResult)
    (capIH : ∀ capResult,
        partialStrengthenTyped? capValue strengthening =
            some capResult →
          StrengtheningSoundness capResult)
    (result : StrengtheningResult strengthening
      (Term.hcomp (context := sourceCtx) (carrierType := carrierType)
        (sidesRaw := sidesRaw) (capRaw := capRaw) modeIsUnivalent
        sidesValue capValue))
    (success : partialStrengthenTyped?
        (Term.hcomp (context := sourceCtx) (carrierType := carrierType)
          (sidesRaw := sidesRaw) (capRaw := capRaw) modeIsUnivalent
          sidesValue capValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i sidesResult sidesRecurse
    split at success
    · cases success
    · rename_i capResult capRecurse
      cases success
      exact partialStrengthenTypedHcomp_sound modeIsUnivalent
        (sidesIH sidesResult sidesRecurse)
        (capIH capResult capRecurse)

/-- Dispatcher soundness at the `Term.hcompPath` arm.  Path-shaped
cubical composition: `sidesPath` lives at `Ty.path carrierType
leftEndpoint rightEndpoint`, so three raw/Ty witnesses thread through
(carrier, left, right), plus two child IHs (sidesPath + capValue).
Mirrors pathLam's 3-witness pattern but at term-level rather than
under a binder.  Wrapper takes both `leftEndpoint`/`rightEndpoint`
explicitly because they are explicit fields of `Term.hcompPath`. -/
theorem partialStrengthenTyped?_atHcompPath_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sidesIH : ∀ sidesPathResult,
        partialStrengthenTyped? sidesPath strengthening =
            some sidesPathResult →
          StrengtheningSoundness sidesPathResult)
    (capIH : ∀ capResult,
        partialStrengthenTyped? capValue strengthening =
            some capResult →
          StrengtheningSoundness capResult)
    (result : StrengtheningResult strengthening
      (Term.hcompPath (context := sourceCtx) (carrierType := carrierType)
        (sidesPathRaw := sidesPathRaw) (capRaw := capRaw)
        modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue))
    (success : partialStrengthenTyped?
        (Term.hcompPath (context := sourceCtx)
          (carrierType := carrierType)
          (sidesPathRaw := sidesPathRaw) (capRaw := capRaw)
          modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue)
          strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrierType carrierSuccess
    split at success
    · cases success
    · rename_i targetLeftEndpoint leftSuccess
      split at success
      · cases success
      · rename_i targetRightEndpoint rightSuccess
        split at success
        · cases success
        · rename_i sidesPathResult sidesRecurse
          split at success
          · cases success
          · rename_i capResult capRecurse
            cases success
            exact partialStrengthenTypedHcompPath_sound
              modeIsUnivalent leftEndpoint rightEndpoint
              carrierSuccess leftSuccess rightSuccess
              (sidesIH sidesPathResult sidesRecurse)
              (capIH capResult capRecurse)

/-- Dispatcher soundness at the `Term.transp` arm.  Heaviest leaf:
cubical transport carries 2 Ty witnesses (sourceType, targetType) +
2 raw witnesses (sourceTypeRaw, targetTypeRaw) + 2 child IHs
(typePath, sourceValue) + metadata (universeLevel, universeLevelLt,
modeIsUnivalent).  Term-level types `sourceType` and `targetType`
are distinct — transp's role is to transport from source to target
along `typePath` — but both still strengthen homogeneously (the
strengthening is a context modification, not a type-shape change). -/
theorem partialStrengthenTyped?_atTransp_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (pathIH : ∀ pathResult,
        partialStrengthenTyped? typePath strengthening =
            some pathResult →
          StrengtheningSoundness pathResult)
    (sourceIH : ∀ sourceResult,
        partialStrengthenTyped? sourceValue strengthening =
            some sourceResult →
          StrengtheningSoundness sourceResult)
    (result : StrengtheningResult strengthening
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw
        targetTypeRaw typePath sourceValue))
    (success : partialStrengthenTyped?
        (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
          universeLevelLt sourceType targetType sourceTypeRaw
          targetTypeRaw typePath sourceValue) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetSourceType sourceTypeSuccess
    split at success
    · cases success
    · rename_i targetTargetType targetTypeSuccess
      split at success
      · cases success
      · rename_i targetSourceTypeRaw sourceTypeRawSuccess
        split at success
        · cases success
        · rename_i targetTargetTypeRaw targetTypeRawSuccess
          split at success
          · cases success
          · rename_i pathResult pathRecurse
            split at success
            · cases success
            · rename_i sourceResult sourceRecurse
              cases success
              exact partialStrengthenTypedTransp_sound modeIsUnivalent
                universeLevel universeLevelLt sourceType targetType
                targetSourceType targetTargetType sourceTypeRaw
                targetTypeRaw targetSourceTypeRaw targetTargetTypeRaw
                sourceTypeSuccess targetTypeSuccess
                sourceTypeRawSuccess targetTypeRawSuccess
                (pathIH pathResult pathRecurse)
                (sourceIH sourceResult sourceRecurse)

/-! ## Headline aggregator infrastructure

The next layer above the 78 per-arm dispatcher leaves
(`partialStrengthenTyped?_at<Ctor>_imp_sound`) is the full structural
aggregator `partialStrengthenTyped?_imp_sound`: for ANY source typed
term, if `partialStrengthenTyped?` succeeds, the result satisfies
`StrengtheningSoundness`.  The aggregator is a 78-case structural
induction on `Term`, with each case applying the corresponding leaf.

Per-ctor IH plumbing varies (0–4 IHs depending on ctor arity and
binder structure), so the per-arm wrappers landed in multiple
phases (Phases 80–90); the universal headline composing all 78
arms via structural induction on `Term` is the next milestone, and
unblocks the long-term image-theorem closure
(`weaken_inv_of_strengthenTyped?_some` →
`strengthenTyped?_some_of_weaken` →
`weaken_image_iff_strengthenTyped?_some`).

This file ships the uniform soundness property `IsAggregatorSound`
plus all 78 per-arm dispatcher wrappers
`isAggregatorSound_<ctor>` covering every Term constructor.  The
headline universal aggregator (`∀ sourceTerm, IsAggregatorSound
sourceTerm`) lands in a follow-up phase as a single structural
induction composing the 78 wrappers. -/

/-- The aggregator-soundness property for a typed source term.

`IsAggregatorSound sourceTerm` asserts that for ANY context
strengthening from `sourceTerm`'s context, ANY successful dispatch
of `partialStrengthenTyped?` produces a result whose recovery
equations hold (via `StrengtheningSoundness`).

The 78 per-arm dispatcher leaves
`partialStrengthenTyped?_at<Ctor>_imp_sound` each prove this
property for terms whose head constructor is the respective ctor,
under inductive hypotheses for the recursive children.

The full aggregator is the headline theorem
`∀ sourceTerm, IsAggregatorSound sourceTerm`, proved by structural
induction on `Term`; this file ships the predicate plus the `var`
base case as scaffolding. -/
def IsAggregatorSound {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {ty : Ty level sourceScope} {rawTerm : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx ty rawTerm) : Prop :=
  ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening sourceTerm),
    partialStrengthenTyped? sourceTerm strengthening = some result →
    StrengtheningSoundness result

/-- Headline aggregator soundness at the `Term.var` arm.

Lifts `partialStrengthenTyped?_atVar_imp_sound` into the uniform
`IsAggregatorSound` predicate shape consumed by downstream image
theorems (Steps 2–4 of `Term.weaken` strengthening invertibility).

The proof is a single-line delegation: `intros _ _ str res suc`
introduces the universally-quantified strengthening / result /
success arguments, then `exact` calls the per-arm leaf.

First of 78 per-arm wrappers; remaining 77 ship across Phases
81–90.  After all 78 wrappers, the universal headline aggregator
composes them via structural induction. -/
theorem isAggregatorSound_var {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (sourcePosition : Fin sourceScope) :
    IsAggregatorSound
      (Term.var (context := sourceCtx) sourcePosition) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atVar_imp_sound sourcePosition
    strengthening result success

/-- Headline aggregator soundness at the `Term.unit` arm.

Lifts `partialStrengthenTyped?_atUnit_imp_sound` into the uniform
`IsAggregatorSound` predicate shape.  Second zero-IH closed-atomic
ctor; confirms the template scales identically to `var` with no
ctor-specific positional arguments — the leaf takes only
strengthening / result / success. -/
theorem isAggregatorSound_unit {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.unit (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUnit_imp_sound strengthening result
    success

/-- Headline aggregator soundness at the `Term.boolTrue` arm. -/
theorem isAggregatorSound_boolTrue {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.boolTrue (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atBoolTrue_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.boolFalse` arm. -/
theorem isAggregatorSound_boolFalse {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.boolFalse (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atBoolFalse_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.natZero` arm. -/
theorem isAggregatorSound_natZero {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.natZero (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atNatZero_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.interval0` arm. -/
theorem isAggregatorSound_interval0 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.interval0 (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atInterval0_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.interval1` arm. -/
theorem isAggregatorSound_interval1 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.interval1 (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atInterval1_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.listNil` arm.  Takes
the element type explicitly (parametric closed value). -/
theorem isAggregatorSound_listNil {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (elementType : Ty level sourceScope) :
    IsAggregatorSound
      (Term.listNil (context := sourceCtx)
        (elementType := elementType)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListNil_imp_sound elementType
    strengthening result success

/-- Headline aggregator soundness at the `Term.optionNone` arm. -/
theorem isAggregatorSound_optionNone {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (elementType : Ty level sourceScope) :
    IsAggregatorSound
      (Term.optionNone (context := sourceCtx)
        (elementType := elementType)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOptionNone_imp_sound elementType
    strengthening result success

/-- Headline aggregator soundness at the `Term.refl` arm.  HoTT
identity-refl: takes carrier type and raw witness as implicits
matching the leaf's signature. -/
theorem isAggregatorSound_refl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    IsAggregatorSound
      (Term.refl (context := sourceCtx) (carrier := carrier)
        rawWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atRefl_imp_sound strengthening result
    success

/-- Headline aggregator soundness at the `Term.oeqRefl` arm.
Observational-equality refl mirrors `refl`. -/
theorem isAggregatorSound_oeqRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    IsAggregatorSound
      (Term.oeqRefl (context := sourceCtx) (carrier := carrier)
        rawWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOeqRefl_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.idStrictRefl` arm.
Strict-mode identity refl carries a mode-equality witness plus
carrier and raw witness. -/
theorem isAggregatorSound_idStrictRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    IsAggregatorSound
      (Term.idStrictRefl (context := sourceCtx) (carrier := carrier)
        modeIsStrict rawWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdStrictRefl_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.equivReflId` arm.
Identity-as-equivalence: carrier-only zero-IH closed-atomic. -/
theorem isAggregatorSound_equivReflId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope} :
    IsAggregatorSound
      (Term.equivReflId (context := sourceCtx)
        (carrier := carrier)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivReflId_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.arrowCode` arm.
Universe-level forwarding + two flat-scope raw witnesses. -/
theorem isAggregatorSound_arrowCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.arrowCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atArrowCode_imp_sound outerLevel levelLe
    domainCodeRaw codomainCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.piTyCode` arm.
One flat-scope raw + one lifted raw (codomain at `scope + 1`). -/
theorem isAggregatorSound_piTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.piTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPiTyCode_imp_sound outerLevel levelLe
    domainCodeRaw codomainCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.sigmaTyCode` arm.
Structurally identical to `piTyCode`. -/
theorem isAggregatorSound_sigmaTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSigmaTyCode_imp_sound outerLevel
    levelLe domainCodeRaw codomainCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.productCode` arm.
Two flat-scope raw witnesses (first + second components). -/
theorem isAggregatorSound_productCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.productCode (context := sourceCtx) outerLevel levelLe
        firstCodeRaw secondCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atProductCode_imp_sound outerLevel
    levelLe firstCodeRaw secondCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.sumCode` arm.
Binary sum: left + right summand codes. -/
theorem isAggregatorSound_sumCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.sumCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSumCode_imp_sound outerLevel levelLe
    leftCodeRaw rightCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.listCode` arm.
Single flat-scope element-code raw. -/
theorem isAggregatorSound_listCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.listCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListCode_imp_sound outerLevel levelLe
    elementCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.optionCode` arm.
Structurally identical to `listCode`. -/
theorem isAggregatorSound_optionCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.optionCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOptionCode_imp_sound outerLevel
    levelLe elementCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.eitherCode` arm.
Two flat-scope summand-code raws. -/
theorem isAggregatorSound_eitherCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.eitherCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEitherCode_imp_sound outerLevel
    levelLe leftCodeRaw rightCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.idCode` arm.
Three flat-scope raws: type-code + left + right endpoints. -/
theorem isAggregatorSound_idCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.idCode (context := sourceCtx) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdCode_imp_sound outerLevel levelLe
    typeCodeRaw leftRaw rightRaw strengthening result success

/-- Headline aggregator soundness at the `Term.equivCode` arm.
Structurally identical to `eitherCode`. -/
theorem isAggregatorSound_equivCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.equivCode (context := sourceCtx) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivCode_imp_sound outerLevel
    levelLe leftTypeCodeRaw rightTypeCodeRaw strengthening result
    success

/-- Headline aggregator soundness at the `Term.universeCode` arm.
Bare universe-of-codes carrying inner/outer level + cumulativity
proof + outer-bound proof; no raw payload. -/
theorem isAggregatorSound_universeCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsAggregatorSound
      (Term.universeCode (context := sourceCtx) innerLevel outerLevel
        cumulOk levelLe) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUniverseCode_imp_sound innerLevel
    outerLevel cumulOk levelLe strengthening result success

/-- Headline aggregator soundness at the `Term.funextRefl` arm.  Two
flat type witnesses + one lifted raw witness at `scope + 1`. -/
theorem isAggregatorSound_funextRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.funextRefl (context := sourceCtx) domainType codomainType
        applyRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFunextRefl_imp_sound domainType
    codomainType applyRaw strengthening result success

/-- Headline aggregator soundness at the `Term.equivReflIdAtId` arm.
Inner-universe-level pair + carrier type + flat raw witness. -/
theorem isAggregatorSound_equivReflIdAtId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel
        innerLevelLt carrier carrierRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivReflIdAtId_imp_sound innerLevel
    innerLevelLt carrier carrierRaw strengthening result success

/-- Headline aggregator soundness at the `Term.funextReflAtId` arm.
Structurally identical to `funextRefl`; differs only in resulting
wrapper type (Id-typed vs canonical funext form). -/
theorem isAggregatorSound_funextReflAtId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.funextReflAtId (context := sourceCtx) domainType
        codomainType applyRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFunextReflAtId_imp_sound domainType
    codomainType applyRaw strengthening result success

/-- Headline aggregator soundness at the `Term.funextIntroHet` arm.
Two flat type witnesses + two lifted raw witnesses at `scope + 1`. -/
theorem isAggregatorSound_funextIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.funextIntroHet (context := sourceCtx) domainType
        codomainType applyARaw applyBRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFunextIntroHet_imp_sound domainType
    codomainType applyARaw applyBRaw strengthening result success

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

/-- Headline aggregator soundness at the `Term.fst` arm.  1-IH
Σ-first-projection (with internal type-shape strengthening). -/
theorem isAggregatorSound_fst {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairAggregator : IsAggregatorSound pairTerm) :
    IsAggregatorSound (Term.fst pairTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFst_imp_sound strengthening
    (pairAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.snd` arm.  1-IH
Σ-second-projection (with internal type-shape strengthening). -/
theorem isAggregatorSound_snd {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairAggregator : IsAggregatorSound pairTerm) :
    IsAggregatorSound (Term.snd pairTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSnd_imp_sound strengthening
    (pairAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.pair` arm.  2-IH
Σ-introduction over `(firstValue, secondValue)`.  `secondValue`'s
type is `secondType.subst0 firstType firstRaw`, threaded
transparently via the aggregator predicate. -/
theorem isAggregatorSound_pair {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstAggregator : IsAggregatorSound firstValue)
    (secondAggregator : IsAggregatorSound secondValue) :
    IsAggregatorSound
      (Term.pair (secondType := secondType) firstValue secondValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPair_imp_sound strengthening
    (firstAggregator strengthening) (secondAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.refineIntro` arm.
2-IH refinement introduction: the `predicate` raw rides
`strengthening.back.lift`; `baseValue` and `predicateProof` each
supply an aggregator. -/
theorem isAggregatorSound_refineIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (baseAggregator : IsAggregatorSound baseValue)
    (proofAggregator : IsAggregatorSound predicateProof) :
    IsAggregatorSound
      (Term.refineIntro predicate baseValue predicateProof) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atRefineIntro_imp_sound strengthening
    (baseAggregator strengthening) (proofAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.intervalOpp` arm.
1-IH interval negation. -/
theorem isAggregatorSound_intervalOpp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerAggregator : IsAggregatorSound innerValue) :
    IsAggregatorSound
      (Term.intervalOpp (innerValue := innerValue)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIntervalOpp_imp_sound strengthening
    (innerAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.intervalMeet` arm.
2-IH interval meet (min). -/
theorem isAggregatorSound_intervalMeet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftAggregator : IsAggregatorSound leftValue)
    (rightAggregator : IsAggregatorSound rightValue) :
    IsAggregatorSound
      (Term.intervalMeet (leftValue := leftValue)
        (rightValue := rightValue)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIntervalMeet_imp_sound strengthening
    (leftAggregator strengthening) (rightAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.intervalJoin` arm.
2-IH interval join (max). -/
theorem isAggregatorSound_intervalJoin {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftAggregator : IsAggregatorSound leftValue)
    (rightAggregator : IsAggregatorSound rightValue) :
    IsAggregatorSound
      (Term.intervalJoin (leftValue := leftValue)
        (rightValue := rightValue)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIntervalJoin_imp_sound strengthening
    (leftAggregator strengthening) (rightAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.listCons` arm.
2-IH list cons (head + tail). -/
theorem isAggregatorSound_listCons {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headAggregator : IsAggregatorSound headTerm)
    (tailAggregator : IsAggregatorSound tailTerm) :
    IsAggregatorSound
      (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListCons_imp_sound strengthening
    (headAggregator strengthening) (tailAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.codataDest` arm.
1-IH codata destruction. -/
theorem isAggregatorSound_codataDest {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataAggregator : IsAggregatorSound codataValue) :
    IsAggregatorSound (Term.codataDest codataValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atCodataDest_imp_sound strengthening
    (codataAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.codataUnfold` arm.
2-IH codata introduction (`initialState` + `transition`). -/
theorem isAggregatorSound_codataUnfold {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (stateAggregator : IsAggregatorSound initialState)
    (transitionAggregator : IsAggregatorSound transition) :
    IsAggregatorSound
      (Term.codataUnfold initialState transition) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atCodataUnfold_imp_sound strengthening
    (stateAggregator strengthening) (transitionAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.pathApp` arm.  2-IH
cubical path application (`pathTerm` + `intervalTerm`); also threads
the `modeIsUnivalent` mode-eq witness. -/
theorem isAggregatorSound_pathApp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathAggregator : IsAggregatorSound pathTerm)
    (intervalAggregator : IsAggregatorSound intervalTerm) :
    IsAggregatorSound
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPathApp_imp_sound strengthening
    (pathAggregator strengthening) (intervalAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.glueElim` arm.
1-IH cubical glue elimination, threading `modeIsUnivalent`. -/
theorem isAggregatorSound_glueElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {gluedValue :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedAggregator : IsAggregatorSound gluedValue) :
    IsAggregatorSound (Term.glueElim modeIsUnivalent gluedValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atGlueElim_imp_sound strengthening
    (gluedAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.uaToEquiv` arm.
1-IH (proof of type identity) with positional universe-level data
(`innerLevel`/`innerLevelLt`), two carrier types, two raw type
witnesses. -/
theorem isAggregatorSound_uaToEquiv {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw
          rightTyRaw) proofRaw}
    (proofAggregator : IsAggregatorSound proof) :
    IsAggregatorSound
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUaToEquiv_imp_sound innerLevel
    innerLevelLt leftTy rightTy leftTyRaw rightTyRaw strengthening
    (proofAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.transp` arm.  2-IH
cubical transport: `typePath` (universe-valued path) + `sourceValue`
(input at sourceType); positional `modeIsUnivalent` /
`universeLevel` / `universeLevelLt` / `sourceType` / `targetType` /
`sourceTypeRaw` / `targetTypeRaw`. -/
theorem isAggregatorSound_transp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw) pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (pathAggregator : IsAggregatorSound typePath)
    (sourceAggregator : IsAggregatorSound sourceValue) :
    IsAggregatorSound
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw
        targetTypeRaw typePath sourceValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atTransp_imp_sound modeIsUnivalent
    universeLevel universeLevelLt sourceType targetType sourceTypeRaw
    targetTypeRaw strengthening (pathAggregator strengthening)
    (sourceAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.app` arm.  2-IH
non-dependent application (function + argument). -/
theorem isAggregatorSound_app {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionAggregator : IsAggregatorSound functionTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound
      (Term.app (codomainType := codomainType) functionTerm
        argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atApp_imp_sound strengthening
    (functionAggregator strengthening)
    (argumentAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.appPi` arm.  2-IH
dependent application; codomain rides under the binder. -/
theorem isAggregatorSound_appPi {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionAggregator : IsAggregatorSound functionTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound
      (Term.appPi (codomainType := codomainType) functionTerm
        argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atAppPi_imp_sound strengthening
    (functionAggregator strengthening)
    (argumentAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.sessionSend` arm.
2-IH session send (`channel` + `payload`); `protocolStep` is a raw
witness threading through the leaf. -/
theorem isAggregatorSound_sessionSend {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelAggregator : IsAggregatorSound channel)
    (payloadAggregator : IsAggregatorSound payload) :
    IsAggregatorSound
      (Term.sessionSend protocolStep channel payload) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSessionSend_imp_sound strengthening
    (channelAggregator strengthening)
    (payloadAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.sessionRecv` arm.
1-IH session receive (`channel` only); `protocolStep` carries the
raw witness through. -/
theorem isAggregatorSound_sessionRecv {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelAggregator : IsAggregatorSound channel) :
    IsAggregatorSound (Term.sessionRecv channel) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSessionRecv_imp_sound strengthening
    (channelAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.glueIntro` arm.  2-IH
cubical glue introduction (`baseValue` + `partialValue`, both at
`baseType`); `modeIsUnivalent` is positional, `baseType` and
`boundaryWitness` are implicit (inferred from `baseValue`'s type). -/
theorem isAggregatorSound_glueIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseAggregator : IsAggregatorSound baseValue)
    (partialAggregator : IsAggregatorSound partialValue) :
    IsAggregatorSound
      (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
        boundaryWitness baseValue partialValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atGlueIntro_imp_sound modeIsUnivalent
    strengthening (baseAggregator strengthening)
    (partialAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.lam` arm.  Lambda
binder: body lives under `sourceCtx.cons domainType`.  The body
aggregator must absorb the strengthening through the lift; the
wrapper threads `bodyAggregator (strengthening.lift domainType ...)`. -/
theorem isAggregatorSound_lam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyAggregator : IsAggregatorSound body) :
    IsAggregatorSound
      (Term.lam (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atLam_imp_sound strengthening
    (fun targetDomainType domainSuccess bodyResult bodyRecurse =>
      bodyAggregator
        (strengthening.lift domainType targetDomainType domainSuccess)
        bodyResult bodyRecurse)
    result success

/-- Headline aggregator soundness at the `Term.lamPi` arm.
Dependent-Π lambda: body lives at codomain inside the binder. -/
theorem isAggregatorSound_lamPi {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (bodyAggregator : IsAggregatorSound body) :
    IsAggregatorSound
      (Term.lamPi (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atLamPi_imp_sound strengthening
    (fun targetDomainType domainSuccess bodyResult bodyRecurse =>
      bodyAggregator
        (strengthening.lift domainType targetDomainType domainSuccess)
        bodyResult bodyRecurse)
    result success

/-- Headline aggregator soundness at the `Term.pathLam` arm.  Cubical
path-lambda binder: body lives under `sourceCtx.cons Ty.interval`.
The interval slot is fixed (no domain strengthening), so the body
aggregator threads against `strengthening.lift Ty.interval
Ty.interval rfl`. -/
theorem isAggregatorSound_pathLam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyAggregator : IsAggregatorSound body) :
    IsAggregatorSound
      (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPathLam_imp_sound modeIsUnivalent
    strengthening
    (fun bodyResult bodyRecurse =>
      bodyAggregator
        (strengthening.lift Ty.interval Ty.interval rfl)
        bodyResult bodyRecurse)
    result success

/-- Aggregator wrapper at the `Term.boolElim` arm.  Three flat-context
value IHs (scrutinee + then + else); motive is a `Ty (sourceScope + 1)`
handled by the dispatcher leaf's internal type-witness split, so no
motive aggregator. -/
theorem isAggregatorSound_boolElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (thenAggregator : IsAggregatorSound thenBranch)
    (elseAggregator : IsAggregatorSound elseBranch) :
    IsAggregatorSound
      (Term.boolElim (motiveType := motiveType) scrutinee thenBranch
        elseBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atBoolElim_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (thenAggregator strengthening)
    (elseAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.natElim` arm.  Three flat-context
value IHs (scrutinee + zero + succ); succ branch has the eliminator's
arrow `Ty.nat → motiveType`. -/
theorem isAggregatorSound_natElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (zeroAggregator : IsAggregatorSound zeroBranch)
    (succAggregator : IsAggregatorSound succBranch) :
    IsAggregatorSound
      (Term.natElim (motiveType := motiveType) scrutinee zeroBranch
        succBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atNatElim_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (zeroAggregator strengthening)
    (succAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.natRec` arm.  Mirrors `atNatElim`
shape with the recursor's higher-kinded succ branch
`Ty.nat → motiveType → motiveType`. -/
theorem isAggregatorSound_natRec {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (zeroAggregator : IsAggregatorSound zeroBranch)
    (succAggregator : IsAggregatorSound succBranch) :
    IsAggregatorSound
      (Term.natRec (motiveType := motiveType) scrutinee zeroBranch
        succBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atNatRec_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (zeroAggregator strengthening)
    (succAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.listElim` arm.  Parametric ι-
eliminator: one element-type witness handled internally by the leaf
plus three flat-context value IHs (scrutinee + nil + cons). -/
theorem isAggregatorSound_listElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (nilAggregator : IsAggregatorSound nilBranch)
    (consAggregator : IsAggregatorSound consBranch) :
    IsAggregatorSound
      (Term.listElim (motiveType := motiveType) scrutinee nilBranch
        consBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListElim_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (nilAggregator strengthening)
    (consAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.optionMatch` arm.  Mirrors
`atListElim` shape: one element-type witness internal + three flat-
context value IHs (scrutinee + none + some). -/
theorem isAggregatorSound_optionMatch {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (noneAggregator : IsAggregatorSound noneBranch)
    (someAggregator : IsAggregatorSound someBranch) :
    IsAggregatorSound
      (Term.optionMatch (motiveType := motiveType) scrutinee noneBranch
        someBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOptionMatch_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (noneAggregator strengthening)
    (someAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.eitherMatch` arm.  Two-source
parametric ι-eliminator: two type witnesses (leftType + rightType)
handled internally plus three flat-context value IHs (scrutinee +
left + right). -/
theorem isAggregatorSound_eitherMatch {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeAggregator : IsAggregatorSound scrutinee)
    (leftAggregator : IsAggregatorSound leftBranch)
    (rightAggregator : IsAggregatorSound rightBranch) :
    IsAggregatorSound
      (Term.eitherMatch (motiveType := motiveType) scrutinee leftBranch
        rightBranch) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEitherMatch_imp_sound strengthening
    (scrutineeAggregator strengthening)
    (leftAggregator strengthening)
    (rightAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.idJ` arm.  HoTT J-eliminator: two
flat-context value IHs (baseCase + witness); type witnesses (carrier +
both endpoints) are handled internally by the leaf via the
`strengthening`-driven splits, so no companion aggregators. -/
theorem isAggregatorSound_idJ {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseAggregator : IsAggregatorSound baseCase)
    (witnessAggregator : IsAggregatorSound witness) :
    IsAggregatorSound
      (Term.idJ (motiveType := motiveType) baseCase witness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdJ_imp_sound strengthening
    (baseAggregator strengthening)
    (witnessAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.oeqJ` arm.  Mirrors `atIdJ` for
observational equality: two flat-context value IHs (baseCase +
witness). -/
theorem isAggregatorSound_oeqJ {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseAggregator : IsAggregatorSound baseCase)
    (witnessAggregator : IsAggregatorSound witness) :
    IsAggregatorSound
      (Term.oeqJ (motiveType := motiveType) baseCase witness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOeqJ_imp_sound strengthening
    (baseAggregator strengthening)
    (witnessAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.idStrictRec` arm.  Strict-mode
J-eliminator: two flat-context value IHs plus the `modeIsStrict`
discipline witness threaded through. -/
theorem isAggregatorSound_idStrictRec {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseAggregator : IsAggregatorSound baseCase)
    (witnessAggregator : IsAggregatorSound witness) :
    IsAggregatorSound
      (Term.idStrictRec (motiveType := motiveType) modeIsStrict
        baseCase witness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdStrictRec_imp_sound strengthening
    (baseAggregator strengthening)
    (witnessAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.equivApp` arm.  Heterogeneous
equivalence application: two flat-context value IHs (equiv + argument);
both carrier-type witnesses (`carrierA`/`carrierB`) handled inside the
leaf. -/
theorem isAggregatorSound_equivApp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivAggregator : IsAggregatorSound equivTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound (Term.equivApp equivTerm argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivApp_imp_sound strengthening
    (equivAggregator strengthening)
    (argumentAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.equivApply` arm.  Univalence-
flavoured equivalence application: same shape as `equivApp` — two
flat-context value IHs.  Differs from `equivApp` only in the raw
constructor used by the dispatcher. -/
theorem isAggregatorSound_equivApply {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm :
      Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivAggregator : IsAggregatorSound equivTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound (Term.equivApply equivTerm argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivApply_imp_sound strengthening
    (equivAggregator strengthening)
    (argumentAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.equivIntroHet` arm.  Heterogeneous
equivalence introduction: four function-shaped value IHs (forward +
backward + leftInverse + rightInverse).  Both carrier types handled
internally. -/
theorem isAggregatorSound_equivIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardAggregator : IsAggregatorSound forward)
    (backwardAggregator : IsAggregatorSound backward)
    (leftInvAggregator : IsAggregatorSound leftInv)
    (rightInvAggregator : IsAggregatorSound rightInv) :
    IsAggregatorSound
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivIntroHet_imp_sound strengthening
    (forwardAggregator strengthening)
    (backwardAggregator strengthening)
    (leftInvAggregator strengthening)
    (rightInvAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.oeqFunext` arm.  Observational-
equality funext: one value IH on the pointwise-equality proof.  All
type and raw witnesses handled internally by the leaf's sequential
splits. -/
theorem isAggregatorSound_oeqFunext {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {leftFunctionRaw rightFunctionRaw : RawTerm sourceScope}
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (pointwiseAggregator : IsAggregatorSound pointwiseProof) :
    IsAggregatorSound
      (Term.oeqFunext (domainType := domainType)
        (codomainType := codomainType)
        (leftFunctionRaw := leftFunctionRaw)
        (rightFunctionRaw := rightFunctionRaw)
        pointwiseProof) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOeqFunext_imp_sound strengthening
    (pointwiseAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.uaIntroHet` arm.  Heterogeneous
univalence introduction: one value IH on the equivalence-witness term;
positional `innerLevel`/`innerLevelLt` (universe level + bound) and
the two raw carrier witnesses thread through directly. -/
theorem isAggregatorSound_uaIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivAggregator : IsAggregatorSound equivWitness) :
    IsAggregatorSound
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUaIntroHet_imp_sound innerLevel
    innerLevelLt carrierARaw carrierBRaw strengthening
    (equivAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.effectPerform` arm.  Effect
operation invocation: two flat-context value IHs (operation tag +
arguments); positional `canPerformOperation` predicate threads through
unstrengthened (mode/effect-row metadata). -/
theorem isAggregatorSound_effectPerform {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {effectTag : RawTerm sourceScope}
    {effectRow : Effects.EffectRow}
    {operationSignature :
      Effects.OperationSignature (Ty level sourceScope)}
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationAggregator : IsAggregatorSound operationTag)
    (argumentsAggregator : IsAggregatorSound arguments) :
    IsAggregatorSound
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEffectPerform_imp_sound
    canPerformOperation strengthening
    (operationAggregator strengthening)
    (argumentsAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.hcomp` arm.  Cubical homogeneous
composition: two flat-context value IHs (sides + cap); the
`modeIsUnivalent` discipline witness threads through unstrengthened. -/
theorem isAggregatorSound_hcomp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesAggregator : IsAggregatorSound sidesValue)
    (capAggregator : IsAggregatorSound capValue) :
    IsAggregatorSound
      (Term.hcomp (context := sourceCtx) (carrierType := carrierType)
        (sidesRaw := sidesRaw) (capRaw := capRaw) modeIsUnivalent
        sidesValue capValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atHcomp_imp_sound modeIsUnivalent
    strengthening
    (sidesAggregator strengthening)
    (capAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.hcompPath` arm.  Path-shaped cubical
composition: two flat-context value IHs (sidesPath + cap); positional
`leftEndpoint`/`rightEndpoint` (raw endpoints) thread through, internal
Ty-witness splits for carrier + endpoints handled by the leaf. -/
theorem isAggregatorSound_hcompPath {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesAggregator : IsAggregatorSound sidesPath)
    (capAggregator : IsAggregatorSound capValue) :
    IsAggregatorSound
      (Term.hcompPath (context := sourceCtx) (carrierType := carrierType)
        (sidesPathRaw := sidesPathRaw) (capRaw := capRaw)
        modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atHcompPath_imp_sound modeIsUnivalent
    leftEndpoint rightEndpoint strengthening
    (sidesAggregator strengthening)
    (capAggregator strengthening)
    result success

/-! ## Headline universal aggregator soundness

The universal headline `∀ sourceTerm, IsAggregatorSound sourceTerm`
composes the 78 per-arm `isAggregatorSound_<ctor>` wrappers via
structural induction on `Term`.  Every well-typed source term
satisfies the uniform aggregator-soundness predicate. -/

/-- HEADLINE: every typed Term satisfies `IsAggregatorSound`.

Proved by structural induction on `sourceTerm`, dispatching each
of the 78 constructor arms to its corresponding
`isAggregatorSound_<ctor>` wrapper.  Recursive children supply
their `IsAggregatorSound` certificate via the induction
hypothesis.

This unblocks the image theorem trio (right-inverse soundness,
totality, headline iff) and downstream `Step.eta` cascade
shipments per `extended-roadmap.md` Day 32. -/
theorem isAggregatorSound_universal {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) :
    IsAggregatorSound sourceTerm := by
  induction sourceTerm with
  -- 0-IH closed atomics (wrappers all-implicit)
  | var position => exact isAggregatorSound_var position
  | unit => exact isAggregatorSound_unit
  | boolTrue => exact isAggregatorSound_boolTrue
  | boolFalse => exact isAggregatorSound_boolFalse
  | natZero => exact isAggregatorSound_natZero
  | interval0 => exact isAggregatorSound_interval0
  | interval1 => exact isAggregatorSound_interval1
  -- 0-IH parametric atomics (wrapper takes explicit elementType)
  | listNil => exact isAggregatorSound_listNil _
  | optionNone => exact isAggregatorSound_optionNone _
  -- 0-IH HoTT atomics (wrappers all-implicit; ctor explicits ignored)
  | refl _ _ => exact isAggregatorSound_refl
  | oeqRefl _ _ => exact isAggregatorSound_oeqRefl
  | idStrictRefl _ _ _ => exact isAggregatorSound_idStrictRefl
  | equivReflId _ => exact isAggregatorSound_equivReflId
  -- 0-IH HoTT atomics (wrappers take explicit non-IH args)
  | funextRefl domainType codomainType applyRaw =>
      exact isAggregatorSound_funextRefl domainType codomainType applyRaw
  | equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
      exact isAggregatorSound_equivReflIdAtId innerLevel innerLevelLt
        carrier carrierRaw
  | funextReflAtId domainType codomainType applyRaw =>
      exact isAggregatorSound_funextReflAtId domainType codomainType
        applyRaw
  | funextIntroHet domainType codomainType applyARaw applyBRaw =>
      exact isAggregatorSound_funextIntroHet domainType codomainType
        applyARaw applyBRaw
  -- 0-IH type codes (wrappers all take outerLevel + levelLe + raw forms)
  | arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      exact isAggregatorSound_arrowCode outerLevel levelLe
        domainCodeRaw codomainCodeRaw
  | piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      exact isAggregatorSound_piTyCode outerLevel levelLe
        domainCodeRaw codomainCodeRaw
  | sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
      exact isAggregatorSound_sigmaTyCode outerLevel levelLe
        domainCodeRaw codomainCodeRaw
  | productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
      exact isAggregatorSound_productCode outerLevel levelLe
        firstCodeRaw secondCodeRaw
  | sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      exact isAggregatorSound_sumCode outerLevel levelLe
        leftCodeRaw rightCodeRaw
  | listCode outerLevel levelLe elementCodeRaw =>
      exact isAggregatorSound_listCode outerLevel levelLe elementCodeRaw
  | optionCode outerLevel levelLe elementCodeRaw =>
      exact isAggregatorSound_optionCode outerLevel levelLe elementCodeRaw
  | eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
      exact isAggregatorSound_eitherCode outerLevel levelLe
        leftCodeRaw rightCodeRaw
  | idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
      exact isAggregatorSound_idCode outerLevel levelLe
        typeCodeRaw leftRaw rightRaw
  | equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
      exact isAggregatorSound_equivCode outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw
  | universeCode innerLevel outerLevel cumulOk levelLe =>
      exact isAggregatorSound_universeCode innerLevel outerLevel
        cumulOk levelLe
  -- 1-IH non-binder (wrapper takes only IH)
  | natSucc _ ih => exact isAggregatorSound_natSucc ih
  | optionSome _ ih => exact isAggregatorSound_optionSome ih
  | modIntro _ ih => exact isAggregatorSound_modIntro ih
  | modElim _ ih => exact isAggregatorSound_modElim ih
  | subsume _ ih => exact isAggregatorSound_subsume ih
  | eitherInl _ ih => exact isAggregatorSound_eitherInl ih
  | eitherInr _ ih => exact isAggregatorSound_eitherInr ih
  | recordIntro _ ih => exact isAggregatorSound_recordIntro ih
  | recordProj _ ih => exact isAggregatorSound_recordProj ih
  | refineElim _ ih => exact isAggregatorSound_refineElim ih
  | fst _ ih => exact isAggregatorSound_fst ih
  | snd _ ih => exact isAggregatorSound_snd ih
  | intervalOpp _ ih => exact isAggregatorSound_intervalOpp ih
  | codataDest _ ih => exact isAggregatorSound_codataDest ih
  | sessionRecv _ ih => exact isAggregatorSound_sessionRecv ih
  -- 1-IH cumulUp (5 explicit non-IH params)
  | cumulUp lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh _ ih =>
      exact isAggregatorSound_cumulUp lowerLevel higherLevel
        cumulMonotone levelLeLow levelLeHigh ih
  -- 1-IH uaToEquiv (6 explicit non-IH params + 1 IH)
  | uaToEquiv innerLevel innerLevelLt leftTy rightTy leftTyRaw rightTyRaw _ ih =>
      exact isAggregatorSound_uaToEquiv innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw ih
  -- 1-IH glueElim (1 modeIsUnivalent + 1 IH)
  | glueElim _ _ ih => exact isAggregatorSound_glueElim ih
  -- 2-IH non-binder (wrappers all take 2 IHs)
  | pair _ _ ih1 ih2 => exact isAggregatorSound_pair ih1 ih2
  | listCons _ _ ih1 ih2 => exact isAggregatorSound_listCons ih1 ih2
  | app _ _ ih1 ih2 => exact isAggregatorSound_app ih1 ih2
  | appPi _ _ ih1 ih2 => exact isAggregatorSound_appPi ih1 ih2
  | intervalMeet _ _ ih1 ih2 => exact isAggregatorSound_intervalMeet ih1 ih2
  | intervalJoin _ _ ih1 ih2 => exact isAggregatorSound_intervalJoin ih1 ih2
  | codataUnfold _ _ ih1 ih2 => exact isAggregatorSound_codataUnfold ih1 ih2
  | refineIntro predicate _ _ ih1 ih2 =>
      exact isAggregatorSound_refineIntro predicate ih1 ih2
  | idJ _ _ ih1 ih2 => exact isAggregatorSound_idJ ih1 ih2
  | oeqJ _ _ ih1 ih2 => exact isAggregatorSound_oeqJ ih1 ih2
  | idStrictRec _ _ _ ih1 ih2 => exact isAggregatorSound_idStrictRec ih1 ih2
  | oeqFunext _ _ _ _ _ ih => exact isAggregatorSound_oeqFunext ih
  | sessionSend protocolStep _ _ ih1 ih2 =>
      exact isAggregatorSound_sessionSend protocolStep ih1 ih2
  | equivApp _ _ ih1 ih2 => exact isAggregatorSound_equivApp ih1 ih2
  | equivApply _ _ ih1 ih2 => exact isAggregatorSound_equivApply ih1 ih2
  -- 1-IH uaIntroHet (4 explicit non-IH params + 1 IH)
  | uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw _ ih =>
      exact isAggregatorSound_uaIntroHet innerLevel innerLevelLt
        carrierARaw carrierBRaw ih
  -- 4-IH equivIntroHet (4 Term children)
  | equivIntroHet _ _ _ _ ih1 ih2 ih3 ih4 =>
      exact isAggregatorSound_equivIntroHet ih1 ih2 ih3 ih4
  -- 3-IH eliminators
  | boolElim _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_boolElim ih1 ih2 ih3
  | natElim _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_natElim ih1 ih2 ih3
  | natRec _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_natRec ih1 ih2 ih3
  | listElim _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_listElim ih1 ih2 ih3
  | optionMatch _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_optionMatch ih1 ih2 ih3
  | eitherMatch _ _ _ ih1 ih2 ih3 =>
      exact isAggregatorSound_eitherMatch ih1 ih2 ih3
  -- Effect performance (wrapper only takes canPerformOperation + 2 IH; rest implicit)
  | effectPerform _ _ _ canPerformOperation _ _ ih1 ih2 =>
      exact isAggregatorSound_effectPerform canPerformOperation ih1 ih2
  -- Binders (1-IH body)
  | lam _ ih => exact isAggregatorSound_lam ih
  | lamPi _ ih => exact isAggregatorSound_lamPi ih
  -- Cubical binders/builders (with mode/carrier/endpoint metadata)
  | pathLam modeIsUnivalent _ _ _ _ ih =>
      exact isAggregatorSound_pathLam (modeIsUnivalent := modeIsUnivalent)
        (bodyAggregator := ih)
  | pathApp modeIsUnivalent _ _ ih1 ih2 =>
      exact isAggregatorSound_pathApp (modeIsUnivalent := modeIsUnivalent)
        ih1 ih2
  | glueIntro modeIsUnivalent _ _ _ _ ih1 ih2 =>
      exact isAggregatorSound_glueIntro (modeIsUnivalent := modeIsUnivalent)
        ih1 ih2
  | transp modeIsUnivalent universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw _ _ ih1 ih2 =>
      exact isAggregatorSound_transp (modeIsUnivalent := modeIsUnivalent)
        universeLevel universeLevelLt sourceType targetType
        sourceTypeRaw targetTypeRaw ih1 ih2
  | hcomp modeIsUnivalent _ _ ih1 ih2 =>
      exact isAggregatorSound_hcomp (modeIsUnivalent := modeIsUnivalent)
        ih1 ih2
  | hcompPath modeIsUnivalent leftEndpoint rightEndpoint _ _ ih1 ih2 =>
      exact isAggregatorSound_hcompPath (modeIsUnivalent := modeIsUnivalent)
        leftEndpoint rightEndpoint ih1 ih2

/-! ## Universal totality predicate: `IsAggregatorTotal`.

`IsAggregatorTotal sourceTerm` asserts that for ANY context
strengthening from `sourceTerm`'s context to a target context, and
ANY index strengthening evidence (`sourceType.partialStrengthen?
strengthening.back = some _` and the analogous raw equation), the
typed strengthening dispatcher `partialStrengthenTyped? sourceTerm
strengthening` is guaranteed to return `some _` (not `none`).

This is the totality counterpart to `IsAggregatorSound`: the latter
asserts soundness of a dispatch result conditional on `some`;
`IsAggregatorTotal` asserts the `some` arm always fires when index
witnesses are provided.

The architectural reason for the universal-strengthening shape is
the binder ctors (`Term.lam`, `Term.lamPi`, `Term.pathLam`): their
body's strengthening is the `strengthening.lift` of the parent's,
not a `dropNewest`.  A predicate parameterized only by `newType`
(as in `IsTotalOnWeaken`) cannot transport through the lift; the
universal-strengthening shape can.

Specializing `IsAggregatorTotal sourceTerm` to
`strengthening := ContextStrengthening.dropNewest context newType`
recovers `IsTotalOnWeaken sourceTerm`, so the universal headline
`∀ sourceTerm, IsAggregatorTotal sourceTerm` discharges the
universal `IsTotalOnWeaken` headline by specialization. -/
def IsAggregatorTotal {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw) : Prop :=
  ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    {targetSourceType : Ty level targetScope}
    {targetSourceRaw : RawTerm targetScope},
    sourceType.partialStrengthen? strengthening.back =
        some targetSourceType →
    sourceRaw.partialStrengthen? strengthening.back =
        some targetSourceRaw →
    (partialStrengthenTyped? sourceTerm strengthening).isSome

/-! ## Per-ctor totality wrappers under `IsAggregatorTotal`.

Each of the 78 ctors gets a wrapper.  The wrapper takes any
constructor-specific `IsAggregatorTotal` inductive hypotheses on
recursive children, plus the constructor's positional non-IH data,
and produces `IsAggregatorTotal` for the constructor application. -/

/-- 0-IH closed-atomic totality wrapper: `Term.unit`.  Atomic ctor
with no payload — every strengthening succeeds because the dispatcher
returns `some _` directly. -/
theorem isAggregatorTotal_unit {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.unit (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.boolTrue`. -/
theorem isAggregatorTotal_boolTrue {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.boolTrue (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.boolFalse`. -/
theorem isAggregatorTotal_boolFalse {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.boolFalse (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.natZero`. -/
theorem isAggregatorTotal_natZero {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.natZero (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.interval0`. -/
theorem isAggregatorTotal_interval0 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.interval0 (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH closed-atomic totality wrapper: `Term.interval1`. -/
theorem isAggregatorTotal_interval1 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.interval1 (context := sourceCtx)) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 0-IH variable totality wrapper: `Term.var`.  Requires the
position to survive the strengthening's `back` map — which holds
because we have an index witness for the position's raw form. -/
theorem isAggregatorTotal_var {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (position : Fin sourceScope) :
    IsAggregatorTotal (Term.var (context := sourceCtx) position) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  -- rawStrengthens carries `strengthening.back position = some _`,
  -- which is exactly the dispatcher's surviving arm.
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  · next survives =>
      split
      · next dispatcherSurvives =>
          rw [survives] at dispatcherSurvives
          cases dispatcherSurvives
      · rfl
  · cases rawStrengthens

/-- 1-IH binder totality wrapper: `Term.lam`.  The body's IH supplies
universal-strengthening totality; we instantiate it at the lifted
strengthening with derived domain/codomain witnesses. -/
theorem isAggregatorTotal_lam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyTotal : IsAggregatorTotal body) :
    IsAggregatorTotal
      (Term.lam (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- Extract domainSuccess + codomainSuccess from typeStrengthens.
  unfold partialStrengthenTyped?
  -- typeStrengthens: (Ty.arrow domain codomain).partialStrengthen? back = some _
  -- which unfolds to Option.mapTwo of the children.
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainSuccess, _arrowEq⟩ := Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens: (RawTerm.lam bodyRaw).partialStrengthen? back = some _
  -- which unfolds to a match on body's raw strengthening through .lift.
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetBodyRaw bodyRawSuccess =>
    -- Now we apply bodyTotal at the lifted strengthening.
    -- Need codomainType.weaken strengthens through (strengthening.lift _).back
    -- and bodyRaw strengthens through the same.  Both follow from the
    -- domain/codomain children evidence.
    have codomainWeakenLift :
        codomainType.weaken.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetCodomainType.weaken := by
      change codomainType.weaken.partialStrengthen? strengthening.back.lift =
        some targetCodomainType.weaken
      rw [Ty.partialStrengthen?_weaken_lift codomainType strengthening.back,
        codomainSuccess]
      rfl
    have bodyRawLiftSuccess :
        bodyRaw.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetBodyRaw := bodyRawSuccess
    have bodyTotalCall :=
      bodyTotal
        (strengthening.lift domainType targetDomainType domainSuccess)
        codomainWeakenLift bodyRawLiftSuccess
    -- The dispatcher splits on domain, codomain, body; we discharge each
    -- failure branch as impossible.
    split
    · next domainFails =>
        rw [domainSuccess] at domainFails; cases domainFails
    · next targetDomainAgain domainSucceedsAgain =>
        rw [domainSuccess] at domainSucceedsAgain
        cases domainSucceedsAgain
        split
        · next codomainFails =>
            rw [codomainSuccess] at codomainFails; cases codomainFails
        · next _ _ =>
            split
            · next bodyFails =>
                -- bodyFails contradicts bodyTotalCall via isSome.
                rw [bodyFails] at bodyTotalCall
                cases bodyTotalCall
            · rfl

/-- 1-IH binder totality wrapper: `Term.lamPi`.  Dependent lambda;
the codomain lives inside the binder, so the lifted strengthening
already strengthens it (no double weakening). -/
theorem isAggregatorTotal_lamPi {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (bodyTotal : IsAggregatorTotal body) :
    IsAggregatorTotal
      (Term.lamPi (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold partialStrengthenTyped?
  -- typeStrengthens: (Ty.piTy domain codomain).partialStrengthen? back = some _
  -- piTy strengthens via Option.mapTwo (domain..back) (codomain..back.lift) Ty.piTy
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainLiftSuccess, _piEq⟩ := Option.mapTwo_eq_some typeStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetBodyRaw bodyRawSuccess =>
    -- codomainLiftSuccess already gives us what we need.
    have codomainSuccessAtLift :
        codomainType.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetCodomainType := codomainLiftSuccess
    have bodyRawLiftSuccess :
        bodyRaw.partialStrengthen?
            (strengthening.lift domainType targetDomainType
              domainSuccess).back =
          some targetBodyRaw := bodyRawSuccess
    have bodyTotalCall :=
      bodyTotal
        (strengthening.lift domainType targetDomainType domainSuccess)
        codomainSuccessAtLift bodyRawLiftSuccess
    split
    · next domainFails =>
        rw [domainSuccess] at domainFails; cases domainFails
    · next targetDomainAgain domainSucceedsAgain =>
        rw [domainSuccess] at domainSucceedsAgain
        cases domainSucceedsAgain
        split
        · next bodyFails =>
            rw [bodyFails] at bodyTotalCall
            cases bodyTotalCall
        · rfl

/-- 1-IH binder totality wrapper: `Term.pathLam`.  Cubical path
lambda; the body binds an interval slot, with carrier weakened. -/
theorem isAggregatorTotal_pathLam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyTotal : IsAggregatorTotal body) :
    IsAggregatorTotal
      (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold partialStrengthenTyped?
  -- typeStrengthens for Ty.path: Option.mapThree (carrier..) (left..) (right..) Ty.path
  obtain ⟨targetCarrierType, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess, _pathEq⟩ :=
    Option.mapThree_eq_some typeStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetBodyRaw bodyRawSuccess =>
    have carrierWeakenLift :
        carrierType.weaken.partialStrengthen?
            (strengthening.lift Ty.interval Ty.interval rfl).back =
          some targetCarrierType.weaken := by
      change carrierType.weaken.partialStrengthen? strengthening.back.lift =
        some targetCarrierType.weaken
      rw [Ty.partialStrengthen?_weaken_lift carrierType strengthening.back,
        carrierSuccess]
      rfl
    have bodyRawLiftSuccess :
        bodyRaw.partialStrengthen?
            (strengthening.lift Ty.interval Ty.interval rfl).back =
          some targetBodyRaw := bodyRawSuccess
    have bodyTotalCall :=
      bodyTotal (strengthening.lift Ty.interval Ty.interval rfl)
        carrierWeakenLift bodyRawLiftSuccess
    split
    · next carrierFails =>
        rw [carrierSuccess] at carrierFails; cases carrierFails
    · next targetCarrierAgain carrierSucceedsAgain =>
        rw [carrierSuccess] at carrierSucceedsAgain
        cases carrierSucceedsAgain
        split
        · next leftFails =>
            rw [leftSuccess] at leftFails; cases leftFails
        · next targetLeftAgain leftSucceedsAgain =>
            rw [leftSuccess] at leftSucceedsAgain
            cases leftSucceedsAgain
            split
            · next rightFails =>
                rw [rightSuccess] at rightFails; cases rightFails
            · next targetRightAgain rightSucceedsAgain =>
                rw [rightSuccess] at rightSucceedsAgain
                cases rightSucceedsAgain
                split
                · next bodyFails =>
                    rw [bodyFails] at bodyTotalCall
                    cases bodyTotalCall
                · rfl

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

/-! ## Wave T2: 0-IH parametric atomic totality wrappers.

These ctors have no Term recursive children but carry one or more
`Ty`/`RawTerm` payloads at the source scope.  The dispatcher inspects
each payload's `partialStrengthen?`; success comes either from
extracting the strengthening witness out of `typeStrengthens`
(when the payload appears in the source type) or from
`rawStrengthens` (when the payload appears in the source raw form). -/

/-- 0-IH parametric atomic totality: `Term.listNil`.  Source type is
`Ty.listType elementType`; the dispatcher inspects
`elementType.partialStrengthen?`.  Extract via the inner match. -/
theorem isAggregatorTotal_listNil {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope} :
    IsAggregatorTotal
      (Term.listNil (context := sourceCtx) (elementType := elementType)) := by
  intros _ _ strengthening _ _ typeStrengthens _
  unfold Ty.partialStrengthen? at typeStrengthens
  split at typeStrengthens
  · next strengthenedElement elementSuccess =>
      unfold partialStrengthenTyped?
      split
      · next elementFails =>
          rw [elementSuccess] at elementFails
          cases elementFails
      · rfl
  · next elementFails =>
      cases typeStrengthens

/-- 0-IH parametric atomic totality: `Term.optionNone`.  Same pattern
as `listNil` — Ty.optionType payload. -/
theorem isAggregatorTotal_optionNone {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope} :
    IsAggregatorTotal
      (Term.optionNone (context := sourceCtx) (elementType := elementType)) := by
  intros _ _ strengthening _ _ typeStrengthens _
  unfold Ty.partialStrengthen? at typeStrengthens
  split at typeStrengthens
  · next strengthenedElement elementSuccess =>
      unfold partialStrengthenTyped?
      split
      · next elementFails =>
          rw [elementSuccess] at elementFails
          cases elementFails
      · rfl
  · next elementFails =>
      cases typeStrengthens

/-! ## Wave T3: 2-IH listCons totality.

Both head (elementType) and tail (Ty.listType elementType) have types
encodable from source type's elementType.  The dispatcher recurses on
each child without splitting on the type payload.  Reconstruct
Ty.listType strengthening from typeStrengthens for the tail IH. -/

/-- 2-IH non-binder totality: `Term.listCons`.  Source type is
`Ty.listType elementType`; head type is `elementType`, tail type is
`Ty.listType elementType` (same as source). -/
theorem isAggregatorTotal_listCons {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headTotal : IsAggregatorTotal headTerm)
    (tailTotal : IsAggregatorTotal tailTerm) :
    IsAggregatorTotal
      (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- Extract elementType strengthening from typeStrengthens.
  have elementSuccessExists : ∃ targetElement,
      elementType.partialStrengthen? strengthening.back = some targetElement := by
    rcases hElem : elementType.partialStrengthen? strengthening.back with _ | tgt
    · simp only [Ty.partialStrengthen?, hElem] at typeStrengthens
      cases typeStrengthens
    · exact ⟨tgt, rfl⟩
  obtain ⟨targetElement, elementSuccess⟩ := elementSuccessExists
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  -- rawStrengthens = Option.mapTwo head tail RawTerm.listCons = some _
  obtain ⟨_, _, headRawSuccess, tailRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have headTotalCall :=
    headTotal strengthening elementSuccess headRawSuccess
  have tailTotalCall :=
    tailTotal strengthening typeStrengthens tailRawSuccess
  split
  · next headFails =>
      rw [headFails] at headTotalCall
      cases headTotalCall
  · next _ _ =>
      split
      · next tailFails =>
          rw [tailFails] at tailTotalCall
          cases tailTotalCall
      · rfl

/-! ## Wave T4: 2-IH non-binder totality (atomic Ty children) -/

/-- 2-IH non-binder totality: `Term.intervalMeet`.  Children have type
`Ty.interval` (atomic); both Ty strengthens are `rfl`. -/
theorem isAggregatorTotal_intervalMeet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftTotal : IsAggregatorTotal leftValue)
    (rightTotal : IsAggregatorTotal rightValue) :
    IsAggregatorTotal
      (Term.intervalMeet (leftValue := leftValue) (rightValue := rightValue)) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  obtain ⟨_, _, leftRawSuccess, rightRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have intervalStrengthens :
      (Ty.interval : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.interval := rfl
  have leftTotalCall :=
    leftTotal strengthening intervalStrengthens leftRawSuccess
  have rightTotalCall :=
    rightTotal strengthening intervalStrengthens rightRawSuccess
  split
  · next leftFails =>
      rw [leftFails] at leftTotalCall
      cases leftTotalCall
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightFails] at rightTotalCall
          cases rightTotalCall
      · rfl

/-- 2-IH non-binder totality: `Term.intervalJoin`.  Mirror of
`intervalMeet`. -/
theorem isAggregatorTotal_intervalJoin {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftTotal : IsAggregatorTotal leftValue)
    (rightTotal : IsAggregatorTotal rightValue) :
    IsAggregatorTotal
      (Term.intervalJoin (leftValue := leftValue) (rightValue := rightValue)) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  obtain ⟨_, _, leftRawSuccess, rightRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have intervalStrengthens :
      (Ty.interval : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.interval := rfl
  have leftTotalCall :=
    leftTotal strengthening intervalStrengthens leftRawSuccess
  have rightTotalCall :=
    rightTotal strengthening intervalStrengthens rightRawSuccess
  split
  · next leftFails =>
      rw [leftFails] at leftTotalCall
      cases leftTotalCall
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightFails] at rightTotalCall
          cases rightTotalCall
      · rfl

/-! ## Wave T5: 0-IH parametric atomic with Ty + Raw payloads (refl-family) -/

/-- 0-IH parametric atomic totality: `Term.refl`.  Source type is
`Ty.id carrier rawWitness rawWitness`; dispatcher inspects carrier
+ rawWitness strengthens.  Extract via Option.mapThree from
typeStrengthens. -/
theorem isAggregatorTotal_refl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal (Term.refl (context := sourceCtx) carrier rawWitness) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, _, carrierSuccess, witnessSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next witnessFails =>
          rw [witnessSuccess] at witnessFails
          cases witnessFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.oeqRefl`.  Same shape as
`refl` — source type `Ty.oeq carrier rawWitness rawWitness`. -/
theorem isAggregatorTotal_oeqRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal (Term.oeqRefl (context := sourceCtx) carrier rawWitness) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, _, carrierSuccess, witnessSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next witnessFails =>
          rw [witnessSuccess] at witnessFails
          cases witnessFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.idStrictRefl`.  Source type
`Ty.idStrict carrier rawWitness rawWitness` plus a `modeIsStrict`
value-level parameter. -/
theorem isAggregatorTotal_idStrictRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier rawWitness) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, _, carrierSuccess, witnessSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next witnessFails =>
          rw [witnessSuccess] at witnessFails
          cases witnessFails
      · rfl

/-! ## Wave T6: 0-IH `Term.universeCode` + `cumulUp` totality. -/

/-- 0-IH totality: `Term.universeCode`.  Atomic ctor — the dispatcher
returns `some _` unconditionally because the source type
`Ty.universe outerLevel levelLe` is closed-atomic (scope-independent)
and the raw form `RawTerm.universeCode innerLevel.toNat` strengthens
trivially. -/
theorem isAggregatorTotal_universeCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsAggregatorTotal (Term.universeCode (context := sourceCtx)
      innerLevel outerLevel cumulOk levelLe) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 1-IH totality: `Term.cumulUp`.  Source raw is
`RawTerm.cumulUpMarker codeRaw`; wrapped type code's type is
`Ty.universe lowerLevel levelLeLow`, closed-atomic. -/
theorem isAggregatorTotal_cumulUp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeTotal : IsAggregatorTotal typeCode) :
    IsAggregatorTotal
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  -- typeCode's type Ty.universe is closed-atomic; strengthening always succeeds.
  have universeStrengthens :
      (Ty.universe lowerLevel levelLeLow : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some (Ty.universe lowerLevel levelLeLow) := rfl
  -- Extract codeRaw strengthens from rawStrengthens (RawTerm.cumulUpMarker).
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetCodeRaw codeRawSuccess =>
    have codeTotalCall :=
      codeTotal strengthening universeStrengthens codeRawSuccess
    unfold partialStrengthenTyped?
    split
    · next codeFails =>
        rw [codeFails] at codeTotalCall
        cases codeTotalCall
    · rfl

/-! ## Wave T7: 0-IH type codes (arrow / piTy / sigmaTy / product / sum /
    list / option / either / id / equiv / equivReflId-family / funext-family). -/

/-- 0-IH totality: `Term.arrowCode`.  Source type is
`Ty.universe outerLevel levelLe` (atomic); raw form
`RawTerm.arrowCode domainCodeRaw codomainCodeRaw`.  Dispatcher splits
on each raw payload's strengthening — both succeed via rawStrengthens
mapTwo decomposition. -/
theorem isAggregatorTotal_arrowCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.arrowCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  -- rawStrengthens unfolds (via @[reducible]) to mapTwo form.
  change Option.mapTwo
      (domainCodeRaw.partialStrengthen? strengthening.back)
      (codomainCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.arrowCode = some _ at rawStrengthens
  obtain ⟨_, _, domainSuccess, codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainSuccess] at codomainFails
          cases codomainFails
      · rfl

/-- 0-IH totality: `Term.piTyCode`.  Same as arrowCode but codomain
strengthens at lifted strengthening (piTy's binder shape). -/
theorem isAggregatorTotal_piTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.piTyCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (domainCodeRaw.partialStrengthen? strengthening.back)
      (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
      RawTerm.piTyCode = some _ at rawStrengthens
  obtain ⟨_, _, domainSuccess, codomainLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainLiftSuccess] at codomainFails
          cases codomainFails
      · rfl

/-- 0-IH totality: `Term.sigmaTyCode`.  Same as piTyCode. -/
theorem isAggregatorTotal_sigmaTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.sigmaTyCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (domainCodeRaw.partialStrengthen? strengthening.back)
      (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
      RawTerm.sigmaTyCode = some _ at rawStrengthens
  obtain ⟨_, _, domainSuccess, codomainLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainLiftSuccess] at codomainFails
          cases codomainFails
      · rfl

/-- 0-IH totality: `Term.productCode`.  Two-arg type code without
binder lifts. -/
theorem isAggregatorTotal_productCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.productCode (context := sourceCtx)
      outerLevel levelLe firstCodeRaw secondCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (firstCodeRaw.partialStrengthen? strengthening.back)
      (secondCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.productCode = some _ at rawStrengthens
  obtain ⟨_, _, firstSuccess, secondSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      rw [firstSuccess] at firstFails
      cases firstFails
  · next _ _ =>
      split
      · next secondFails =>
          rw [secondSuccess] at secondFails
          cases secondFails
      · rfl

/-- 0-IH totality: `Term.sumCode`.  Mirror of productCode. -/
theorem isAggregatorTotal_sumCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.sumCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (leftCodeRaw.partialStrengthen? strengthening.back)
      (rightCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.sumCode = some _ at rawStrengthens
  obtain ⟨_, _, leftSuccess, rightSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      rw [leftSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-- 0-IH totality: `Term.listCode`.  Single raw payload. -/
theorem isAggregatorTotal_listCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.listCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some renamed => some (RawTerm.listCode renamed)
          | none => none) = some _ at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetElementCodeRaw elementSuccess =>
    unfold partialStrengthenTyped?
    split
    · next elementFails =>
        rw [elementSuccess] at elementFails
        cases elementFails
    · rfl

/-- 0-IH totality: `Term.optionCode`.  Single raw payload. -/
theorem isAggregatorTotal_optionCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.optionCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some renamed => some (RawTerm.optionCode renamed)
          | none => none) = some _ at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetElementCodeRaw elementSuccess =>
    unfold partialStrengthenTyped?
    split
    · next elementFails =>
        rw [elementSuccess] at elementFails
        cases elementFails
    · rfl

/-- 0-IH totality: `Term.eitherCode`.  Two raw payloads. -/
theorem isAggregatorTotal_eitherCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.eitherCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (leftCodeRaw.partialStrengthen? strengthening.back)
      (rightCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.eitherCode = some _ at rawStrengthens
  obtain ⟨_, _, leftSuccess, rightSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      rw [leftSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-- 0-IH totality: `Term.idCode`.  Three raw payloads (type code,
left endpoint, right endpoint).  Use mapThree. -/
theorem isAggregatorTotal_idCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.idCode (context := sourceCtx)
      outerLevel levelLe typeCodeRaw leftRaw rightRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapThree
      (typeCodeRaw.partialStrengthen? strengthening.back)
      (leftRaw.partialStrengthen? strengthening.back)
      (rightRaw.partialStrengthen? strengthening.back)
      RawTerm.idCode = some _ at rawStrengthens
  obtain ⟨_, _, _, typeCodeSuccess, leftSuccess, rightSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next typeCodeFails =>
      rw [typeCodeSuccess] at typeCodeFails
      cases typeCodeFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · rfl

/-- 0-IH totality: `Term.equivCode`.  Two raw payloads (left/right
type codes). -/
theorem isAggregatorTotal_equivCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.equivCode (context := sourceCtx)
      outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (leftTypeCodeRaw.partialStrengthen? strengthening.back)
      (rightTypeCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.equivCode = some _ at rawStrengthens
  obtain ⟨_, _, leftSuccess, rightSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      rw [leftSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-! ## Wave T8: 2-IH pair totality (dependent Σ-intro).

`Term.pair firstValue secondValue` has source type
`Ty.sigmaTy firstType secondType`.  The first child's type is the
encodable `firstType`; the second child's type is the substituted
`secondType.subst0 firstType firstRaw` — reconstructed via
`Ty.partialStrengthen?_subst0_of_success` using strengthening's
forward/injectsBack/back_forward fields. -/

/-- 2-IH non-binder totality: `Term.pair`.  Combines firstType +
secondType.lift strengthens (from sigmaTy typeStrengthens) +
firstRaw / secondRaw strengthens (from pair rawStrengthens), applying
the subst0 reconstruction lemma to manufacture secondValue's IH input. -/
theorem isAggregatorTotal_pair {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstTotal : IsAggregatorTotal firstValue)
    (secondTotal : IsAggregatorTotal secondValue) :
    IsAggregatorTotal
      (Term.pair (firstValue := firstValue) (secondValue := secondValue)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨targetFirstType, targetSecondType, firstSuccess, secondLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (firstRaw.partialStrengthen? strengthening.back)
      (secondRaw.partialStrengthen? strengthening.back)
      RawTerm.pair = some _ at rawStrengthens
  obtain ⟨targetFirstRaw, targetSecondRaw, firstRawSuccess, secondRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have firstTotalCall :=
    firstTotal strengthening firstSuccess firstRawSuccess
  -- Reconstruct secondType.subst0 strengthens via the subst0 lemma.
  have substStrengthens :
      (secondType.subst0 firstType firstRaw).partialStrengthen?
          strengthening.back =
        some (targetSecondType.subst0 targetFirstType targetFirstRaw) :=
    Ty.partialStrengthen?_subst0_of_success secondType targetSecondType
      firstType targetFirstType firstRaw targetFirstRaw
      strengthening.forward strengthening.back strengthening.injectsBack
      strengthening.back_forward secondLiftSuccess firstSuccess firstRawSuccess
  have secondTotalCall :=
    secondTotal strengthening substStrengthens secondRawSuccess
  unfold partialStrengthenTyped?
  split
  · next secondTypeFails =>
      rw [secondLiftSuccess] at secondTypeFails
      cases secondTypeFails
  · next _ _ =>
      split
      · next firstFails =>
          rw [firstFails] at firstTotalCall
          cases firstTotalCall
      · next _ _ =>
          split
          · next secondFails =>
              rw [secondFails] at secondTotalCall
              cases secondTotalCall
          · rfl

/-- 0-IH totality: `Term.equivReflId`.  Source type
`Ty.equiv carrier carrier` — single carrier component duplicated.
Dispatcher splits on carrier.strengthens which decomposes from
typeStrengthens mapTwo. -/
theorem isAggregatorTotal_equivReflId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) :
    IsAggregatorTotal (Term.equivReflId (context := sourceCtx) carrier) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, carrierSuccess, _, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · rfl

/-- 2-IH totality: `Term.refineIntro`.  Source type
`Ty.refine baseType predicate` — typeStrengthens decomposes via
mapTwo (baseType + predicate.lift).  predicateProof has type
`Ty.unit` (trivially strengthens). -/
theorem isAggregatorTotal_refineIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (baseTotal : IsAggregatorTotal baseValue)
    (proofTotal : IsAggregatorTotal predicateProof) :
    IsAggregatorTotal
      (Term.refineIntro predicate baseValue predicateProof) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨_, _, baseSuccess, predicateLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (valueRaw.partialStrengthen? strengthening.back)
      (proofRaw.partialStrengthen? strengthening.back)
      RawTerm.refineIntro = some _ at rawStrengthens
  obtain ⟨_, _, valueRawSuccess, proofRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have baseTotalCall :=
    baseTotal strengthening baseSuccess valueRawSuccess
  have unitStrengthens :
      (Ty.unit : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.unit := rfl
  have proofTotalCall :=
    proofTotal strengthening unitStrengthens proofRawSuccess
  unfold partialStrengthenTyped?
  split
  · next predicateFails =>
      rw [predicateLiftSuccess] at predicateFails
      cases predicateFails
  · next _ _ =>
      split
      · next baseFails =>
          rw [baseFails] at baseTotalCall
          cases baseTotalCall
      · next _ _ =>
          split
          · next proofFails =>
              rw [proofFails] at proofTotalCall
              cases proofTotalCall
          · rfl

/-- 2-IH totality: `Term.codataUnfold`.  Source type
`Ty.codata stateType outputType` — typeStrengthens decomposes via
mapTwo (stateType + outputType).  initialState's type is stateType;
transition's type is `Ty.arrow stateType outputType` (built via
mapTwo). -/
theorem isAggregatorTotal_codataUnfold {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition : Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (stateTotal : IsAggregatorTotal initialState)
    (transitionTotal : IsAggregatorTotal transition) :
    IsAggregatorTotal
      (Term.codataUnfold (initialState := initialState) (transition := transition)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  obtain ⟨targetStateType, targetOutputType, stateSuccess, outputSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (stateRaw.partialStrengthen? strengthening.back)
      (transitionRaw.partialStrengthen? strengthening.back)
      RawTerm.codataUnfold = some _ at rawStrengthens
  obtain ⟨_, _, stateRawSuccess, transitionRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have stateTotalCall :=
    stateTotal strengthening stateSuccess stateRawSuccess
  have arrowStrengthens :
      (Ty.arrow stateType outputType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetStateType targetOutputType) := by
    show Option.mapTwo
        (stateType.partialStrengthen? strengthening.back)
        (outputType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [stateSuccess, outputSuccess]
    rfl
  have transitionTotalCall :=
    transitionTotal strengthening arrowStrengthens transitionRawSuccess
  unfold partialStrengthenTyped?
  split
  · next outputFails =>
      rw [outputSuccess] at outputFails
      cases outputFails
  · next _ _ =>
      split
      · next stateFails =>
          rw [stateFails] at stateTotalCall
          cases stateTotalCall
      · next _ _ =>
          split
          · next transitionFails =>
              rw [transitionFails] at transitionTotalCall
              cases transitionTotalCall
          · rfl

/-! ## Wave Y1: wrap-able 0-IH/2-IH totality wrappers for ctors whose
    source type fully encodes the dispatcher's index witnesses.

    Each wrapper below decomposes `typeStrengthens` / `rawStrengthens`
    via Option.mapTwo / mapThree inversion plus `Ty.partialStrengthen?_weaken_lift`
    where the source type uses a lifted (binder) sub-Ty.  No additional
    auxiliary witnesses required — the predicate IsAggregatorTotal already
    encodes everything the dispatcher arm reads. -/

/-- 0-IH totality: `Term.funextRefl`.  Source type
`funextReflType domainType codomainType applyRaw = Ty.piTy domainType
(Ty.id codomainType.weaken applyRaw applyRaw)`.  Decompose typeStrengthens
via Ty.piTy mapTwo → domainStrengthens + (Ty.id ...).back.lift = some _.
The latter via Ty.id mapThree → codomainType.weaken.back.lift = some _ +
applyRaw.back.lift = some _ (twice).  Recover codomainStrengthens via
`Ty.partialStrengthen?_weaken_lift` (codomainType.weaken.back.lift =
codomainType.back |>.map weaken; map = some ⟹ inner = some).  Recover
applyRaw.back.lift from rawStrengthens (`RawTerm.lam (RawTerm.refl _)`)
or directly from typeStrengthens. -/
theorem isAggregatorTotal_funextRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.funextRefl (context := sourceCtx)
      domainType codomainType applyRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  -- typeStrengthens : (Ty.piTy domainType (Ty.id codomainType.weaken applyRaw applyRaw)).back = some _
  -- Decompose via Ty.piTy mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      ((Ty.id codomainType.weaken applyRaw applyRaw).partialStrengthen?
        strengthening.back.lift)
      Ty.piTy = some _ at typeStrengthens
  obtain ⟨targetDomainType, targetIdBody, domainSuccess, idSuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  -- Decompose idSuccess via Ty.id mapThree
  change Option.mapThree
      (codomainType.weaken.partialStrengthen? strengthening.back.lift)
      (applyRaw.partialStrengthen? strengthening.back.lift)
      (applyRaw.partialStrengthen? strengthening.back.lift)
      Ty.id = some _ at idSuccess
  obtain ⟨targetCodomainWeaken, targetApplyRaw, _, codomainWeakenSuccess,
    applyRawSuccess, _, _⟩ :=
    Option.mapThree_eq_some idSuccess
  -- Recover codomainType.partialStrengthen? back = some _ via weaken_lift
  rw [Ty.partialStrengthen?_weaken_lift codomainType strengthening.back]
    at codomainWeakenSuccess
  obtain ⟨targetCodomainType, codomainSuccess, _⟩ :=
    Option.map_eq_some_inversion codomainWeakenSuccess
  -- Now discharge the dispatcher
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainSuccess] at codomainFails
          cases codomainFails
      · next _ _ =>
          split
          · next applyFails =>
              rw [applyRawSuccess] at applyFails
              cases applyFails
          · rfl

/-- 0-IH totality: `Term.funextReflAtId`.  Source type
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam (RawTerm.refl applyRaw))
(RawTerm.lam (RawTerm.refl applyRaw))`.  Decompose typeStrengthens via
Ty.id mapThree → arrow.back + two lam-refl raw witnesses.  Ty.arrow.mapTwo
gives dom.back + codom.back.  Either lam-refl raw witness decomposes
to applyRaw.back.lift. -/
theorem isAggregatorTotal_funextReflAtId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.funextReflAtId (context := sourceCtx)
      domainType codomainType applyRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  -- Decompose typeStrengthens via Ty.id mapThree
  change Option.mapThree
      ((Ty.arrow domainType codomainType).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam (RawTerm.refl applyRaw)).partialStrengthen?
        strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, lamWitness, _, arrowSuccess, lamSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- Decompose arrowSuccess via Ty.arrow mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      (codomainType.partialStrengthen? strengthening.back)
      Ty.arrow = some _ at arrowSuccess
  obtain ⟨_, _, domainSuccess, codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some arrowSuccess
  -- Decompose lamSuccess (RawTerm.lam → RawTerm.refl → applyRaw at lift)
  unfold RawTerm.partialStrengthen? at lamSuccess
  unfold RawTerm.partialRename? at lamSuccess
  split at lamSuccess
  rotate_left
  · cases lamSuccess
  next reflWitness reflSuccess =>
    unfold RawTerm.partialRename? at reflSuccess
    split at reflSuccess
    rotate_left
    · cases reflSuccess
    next targetApplyRaw applyRawSuccess =>
      have applyStrengthenSuccess :
          applyRaw.partialStrengthen? strengthening.back.lift =
            some targetApplyRaw := applyRawSuccess
      -- Now discharge the dispatcher
      unfold partialStrengthenTyped?
      split
      · next domainFails =>
          rw [domainSuccess] at domainFails
          cases domainFails
      · next _ _ =>
          split
          · next codomainFails =>
              rw [codomainSuccess] at codomainFails
              cases codomainFails
          · next _ _ =>
              split
              · next applyFails =>
                  rw [applyStrengthenSuccess] at applyFails
                  cases applyFails
              · rfl

/-- 2-IH totality: `Term.hcomp`.  Source type is the carrier `carrierType`
directly, and the dispatcher arm reads NO sub-Ty witnesses (only its
two IH children).  Both children share the carrier as their type, so
both IHs invoke with typeStrengthens directly.  Raw form
`RawTerm.hcomp sidesRaw capRaw` decomposes mapTwo. -/
theorem isAggregatorTotal_hcomp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesTotal : IsAggregatorTotal sidesValue)
    (capTotal : IsAggregatorTotal capValue) :
    IsAggregatorTotal (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (sidesRaw.partialStrengthen? strengthening.back)
      (capRaw.partialStrengthen? strengthening.back)
      RawTerm.hcomp = some _ at rawStrengthens
  obtain ⟨_, _, sidesRawSuccess, capRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have sidesTotalCall :=
    sidesTotal strengthening typeStrengthens sidesRawSuccess
  have capTotalCall :=
    capTotal strengthening typeStrengthens capRawSuccess
  unfold partialStrengthenTyped?
  split
  · next sidesFails =>
      rw [sidesFails] at sidesTotalCall
      cases sidesTotalCall
  · next _ _ =>
      split
      · next capFails =>
          rw [capFails] at capTotalCall
          cases capTotalCall
      · rfl

/-- 1-IH totality: `Term.oeqFunext`.  Source type
`Ty.oeq (Ty.arrow domainType codomainType) leftFunctionRaw rightFunctionRaw`.
Dispatcher needs dom/codom/left/right.back + pointwiseProof IH.
pointwiseProof's type is `oeqFunextPointwiseType` (a piTy of dom with
oeq codom.weaken (app leftRaw.weaken (var 0)) (app rightRaw.weaken (var 0))
in body).  We synthesize the type strengthening via Ty.partialStrengthen?
unfolding + Ty.partialStrengthen?_weaken_lift +
RawTerm.partialStrengthen?_weaken_lift. -/
theorem isAggregatorTotal_oeqFunext {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    {pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw}
    (pointwiseTotal : IsAggregatorTotal pointwiseProof) :
    IsAggregatorTotal
      (Term.oeqFunext (context := sourceCtx) domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens via Ty.oeq mapThree
  change Option.mapThree
      ((Ty.arrow domainType codomainType).partialStrengthen?
        strengthening.back)
      (leftFunctionRaw.partialStrengthen? strengthening.back)
      (rightFunctionRaw.partialStrengthen? strengthening.back)
      Ty.oeq = some _ at typeStrengthens
  obtain ⟨_, targetLeftFunctionRaw, targetRightFunctionRaw, arrowSuccess,
    leftSuccess', rightSuccess', _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- arrowSuccess via Ty.arrow mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      (codomainType.partialStrengthen? strengthening.back)
      Ty.arrow = some _ at arrowSuccess
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some arrowSuccess
  -- rawStrengthens : (RawTerm.oeqFunext pointwiseRaw).back = some _
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetPointwiseRaw pointwiseRawSuccess =>
    have pointwiseStrengthenSuccess :
        pointwiseRaw.partialStrengthen? strengthening.back =
          some targetPointwiseRaw := pointwiseRawSuccess
    -- Construct pointwiseProof's type strengthening:
    -- oeqFunextPointwiseType.back = piTy of dom + oeq codom.weaken etc.
    have codomainWeakenStrengthens :
        codomainType.weaken.partialStrengthen? strengthening.back.lift =
          some targetCodomainType.weaken := by
      rw [Ty.partialStrengthen?_weaken_lift codomainType strengthening.back,
        codomainSuccess]
      rfl
    have leftWeakenStrengthens :
        leftFunctionRaw.weaken.partialStrengthen? strengthening.back.lift =
          some targetLeftFunctionRaw.weaken := by
      rw [RawTerm.partialStrengthen?_weaken_lift leftFunctionRaw
        strengthening.back, leftSuccess']
      rfl
    have rightWeakenStrengthens :
        rightFunctionRaw.weaken.partialStrengthen?
            strengthening.back.lift =
          some targetRightFunctionRaw.weaken := by
      rw [RawTerm.partialStrengthen?_weaken_lift rightFunctionRaw
        strengthening.back, rightSuccess']
      rfl
    have leftAppStrengthens :
        (RawTerm.app leftFunctionRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
          some (RawTerm.app targetLeftFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
      change
        Option.mapTwo
          (leftFunctionRaw.weaken.partialStrengthen?
            strengthening.back.lift)
          (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
          RawTerm.app =
            some (RawTerm.app targetLeftFunctionRaw.weaken
              (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
      rw [leftWeakenStrengthens]
      rfl
    have rightAppStrengthens :
        (RawTerm.app rightFunctionRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
          some (RawTerm.app targetRightFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
      change
        Option.mapTwo
          (rightFunctionRaw.weaken.partialStrengthen?
            strengthening.back.lift)
          (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
          RawTerm.app =
            some (RawTerm.app targetRightFunctionRaw.weaken
              (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
      rw [rightWeakenStrengthens]
      rfl
    have codomainBodyStrengthens :
        (oeqFunextPointwiseCodomain codomainType
            leftFunctionRaw rightFunctionRaw).partialStrengthen?
            strengthening.back.lift =
          some (oeqFunextPointwiseCodomain targetCodomainType
            targetLeftFunctionRaw targetRightFunctionRaw) := by
      change
        Option.mapThree
          (codomainType.weaken.partialStrengthen?
            strengthening.back.lift)
          ((RawTerm.app leftFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
            ).partialStrengthen? strengthening.back.lift)
          ((RawTerm.app rightFunctionRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
            ).partialStrengthen? strengthening.back.lift)
          Ty.oeq =
            some (oeqFunextPointwiseCodomain targetCodomainType
              targetLeftFunctionRaw targetRightFunctionRaw)
      rw [codomainWeakenStrengthens, leftAppStrengthens,
        rightAppStrengthens]
      rfl
    have pointwiseTypeStrengthens :
        (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw).partialStrengthen?
            strengthening.back =
          some (oeqFunextPointwiseType targetDomainType targetCodomainType
            targetLeftFunctionRaw targetRightFunctionRaw) := by
      change
        Option.mapTwo
          (domainType.partialStrengthen? strengthening.back)
          ((oeqFunextPointwiseCodomain codomainType
              leftFunctionRaw rightFunctionRaw).partialStrengthen?
              strengthening.back.lift)
          Ty.piTy =
            some (oeqFunextPointwiseType targetDomainType
              targetCodomainType targetLeftFunctionRaw
              targetRightFunctionRaw)
      rw [domainSuccess, codomainBodyStrengthens]
      rfl
    have pointwiseTotalCall :=
      pointwiseTotal strengthening pointwiseTypeStrengthens
        pointwiseStrengthenSuccess
    unfold partialStrengthenTyped?
    split
    · next domainFails =>
        rw [domainSuccess] at domainFails
        cases domainFails
    · next _ _ =>
        split
        · next codomainFails =>
            rw [codomainSuccess] at codomainFails
            cases codomainFails
        · next _ _ =>
            split
            · next leftFails =>
                rw [leftSuccess'] at leftFails
                cases leftFails
            · next _ _ =>
                split
                · next rightFails =>
                    rw [rightSuccess'] at rightFails
                    cases rightFails
                · next _ _ =>
                    split
                    · next pointwiseFails =>
                        rw [pointwiseFails] at pointwiseTotalCall
                        cases pointwiseTotalCall
                    · rfl

/-- 0-IH totality: `Term.funextIntroHet`.  Source type
`Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam applyARaw)
(RawTerm.lam applyBRaw)`.  Decompose typeStrengthens via Ty.id mapThree
→ arrow.back + two lam raw witnesses.  Ty.arrow.mapTwo gives dom + codom.
Each lam-raw decomposes (via RawTerm.lam) to applyXRaw at .back.lift. -/
theorem isAggregatorTotal_funextIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.funextIntroHet (context := sourceCtx)
      domainType codomainType applyARaw applyBRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  -- Decompose typeStrengthens via Ty.id mapThree
  change Option.mapThree
      ((Ty.arrow domainType codomainType).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam applyARaw).partialStrengthen?
        strengthening.back)
      ((RawTerm.lam applyBRaw).partialStrengthen?
        strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, _, _, arrowSuccess, lamAOk, lamBOk, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- Decompose arrowSuccess via Ty.arrow mapTwo
  change Option.mapTwo
      (domainType.partialStrengthen? strengthening.back)
      (codomainType.partialStrengthen? strengthening.back)
      Ty.arrow = some _ at arrowSuccess
  obtain ⟨_, _, domainSuccess, codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some arrowSuccess
  -- Decompose lamAOk (RawTerm.lam → applyARaw at lift)
  unfold RawTerm.partialStrengthen? at lamAOk
  unfold RawTerm.partialRename? at lamAOk
  split at lamAOk
  rotate_left
  · cases lamAOk
  next targetApplyARaw applyARawRenSuccess =>
    have applyAStrengthenSuccess :
        applyARaw.partialStrengthen? strengthening.back.lift =
          some targetApplyARaw := applyARawRenSuccess
    -- Decompose lamBOk (RawTerm.lam → applyBRaw at lift)
    unfold RawTerm.partialStrengthen? at lamBOk
    unfold RawTerm.partialRename? at lamBOk
    split at lamBOk
    rotate_left
    · cases lamBOk
    next targetApplyBRaw applyBRawRenSuccess =>
      have applyBStrengthenSuccess :
          applyBRaw.partialStrengthen? strengthening.back.lift =
            some targetApplyBRaw := applyBRawRenSuccess
      -- Discharge the dispatcher
      unfold partialStrengthenTyped?
      split
      · next domainFails =>
          rw [domainSuccess] at domainFails
          cases domainFails
      · next _ _ =>
          split
          · next codomainFails =>
              rw [codomainSuccess] at codomainFails
              cases codomainFails
          · next _ _ =>
              split
              · next applyAFails =>
                  rw [applyAStrengthenSuccess] at applyAFails
                  cases applyAFails
              · next _ _ =>
                  split
                  · next applyBFails =>
                      rw [applyBStrengthenSuccess] at applyBFails
                      cases applyBFails
                  · rfl

/-- 2-IH totality: `Term.glueIntro`.  Source type
`Ty.glue baseType boundaryWitness`; dispatcher needs baseType.back +
boundaryWitness.back + 2 IH children (baseValue, partialValue), both
typed at baseType.  typeStrengthens decomposes via Ty.glue mapTwo. -/
theorem isAggregatorTotal_glueIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseTotal : IsAggregatorTotal baseValue)
    (partialTotal : IsAggregatorTotal partialValue) :
    IsAggregatorTotal
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens : (Ty.glue baseType boundaryWitness).back = some _
  change Option.mapTwo
      (baseType.partialStrengthen? strengthening.back)
      (boundaryWitness.partialStrengthen? strengthening.back)
      Ty.glue = some _ at typeStrengthens
  obtain ⟨targetBaseType, _, baseTypeSuccess, boundarySuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens : (RawTerm.glueIntro baseRaw partialRaw).back = some _
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (partialRaw.partialStrengthen? strengthening.back)
      RawTerm.glueIntro = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, partialRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  -- Both children's type IS baseType
  have baseTotalCall :=
    baseTotal strengthening baseTypeSuccess baseRawSuccess
  have partialTotalCall :=
    partialTotal strengthening baseTypeSuccess partialRawSuccess
  unfold partialStrengthenTyped?
  split
  · next baseTypeFails =>
      rw [baseTypeSuccess] at baseTypeFails
      cases baseTypeFails
  · next _ _ =>
      split
      · next boundaryFails =>
          rw [boundarySuccess] at boundaryFails
          cases boundaryFails
      · next _ _ =>
          split
          · next baseFails =>
              rw [baseFails] at baseTotalCall
              cases baseTotalCall
          · next _ _ =>
              split
              · next partialFails =>
                  rw [partialFails] at partialTotalCall
                  cases partialTotalCall
              · rfl

/-! ## Phase Y.2: Bridge wrappers for ctors whose source type lacks
    sub-Ty / sub-raw witnesses the dispatcher reads.

    These wrappers take per-ctor auxiliary witnesses as additional
    hypotheses (modeled on Agent C's Phase X bridge for
    `isTotalOnWeaken_of_weaken_isAggregatorTotal`).  The wrapper still
    discharges `IsAggregatorTotal` at the source ctor application;
    downstream consumers supply the auxiliary witnesses case-by-case.

    The universal-over-all-source-terms headline
    `∀ t, IsAggregatorTotal t` is NOT shippable for these ctors at the
    current predicate, but per-ctor wrappers with case-specific witness
    construction are.  Consumers route through these wrappers when
    the source-level witnesses are constructible in their context. -/

/-- Bridge totality wrapper for `Term.pathApp`.  The dispatcher arm
needs leftEndpoint.back + rightEndpoint.back + carrierType.back, but
the source type encodes only carrierType.  We take the missing
endpoint strengthenings as additional hypotheses parameterized over
strengthening (universally, matching IsAggregatorTotal's shape).

Consumers satisfy these hypotheses when leftEndpoint and rightEndpoint
have known strengthening behaviour (e.g. when they're proved totally
strengthenable independently). -/
theorem isAggregatorTotal_pathApp_with_endpoints {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathTotal : IsAggregatorTotal pathTerm)
    (intervalTotal : IsAggregatorTotal intervalTerm)
    (leftEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetLeftEndpoint,
          leftEndpoint.partialStrengthen? strengthening.back =
            some targetLeftEndpoint)
    (rightEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetRightEndpoint,
          rightEndpoint.partialStrengthen? strengthening.back =
            some targetRightEndpoint) :
    IsAggregatorTotal
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  intros _ _ strengthening targetCarrierType _ typeStrengthens rawStrengthens
  -- typeStrengthens : carrierType.back = some targetCarrierType
  -- rawStrengthens : (RawTerm.pathApp pathRaw intervalRaw).back = some _
  change Option.mapTwo
      (pathRaw.partialStrengthen? strengthening.back)
      (intervalRaw.partialStrengthen? strengthening.back)
      RawTerm.pathApp = some _ at rawStrengthens
  obtain ⟨_, _, pathRawSuccess, intervalRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  -- Get the endpoint strengthenings from the auxiliary hypotheses
  obtain ⟨targetLeftEndpoint, leftEndpointSuccess⟩ :=
    leftEndpointTotal strengthening typeStrengthens
  obtain ⟨targetRightEndpoint, rightEndpointSuccess⟩ :=
    rightEndpointTotal strengthening typeStrengthens
  -- Construct pathTerm's type strengthening: Ty.path.mapThree
  have pathTypeStrengthens :
      (Ty.path carrierType leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.path targetCarrierType targetLeftEndpoint
          targetRightEndpoint) := by
    show Option.mapThree
        (carrierType.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.path = _
    rw [typeStrengthens, leftEndpointSuccess, rightEndpointSuccess]
    rfl
  -- Construct intervalTerm's type strengthening: Ty.interval is closed-atomic
  have intervalTypeStrengthens :
      (Ty.interval : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.interval := rfl
  have pathTotalCall :=
    pathTotal strengthening pathTypeStrengthens pathRawSuccess
  have intervalTotalCall :=
    intervalTotal strengthening intervalTypeStrengthens intervalRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [typeStrengthens] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftEndpointSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightEndpointSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next pathFails =>
                  rw [pathFails] at pathTotalCall
                  cases pathTotalCall
              · next _ _ =>
                  split
                  · next intervalFails =>
                      rw [intervalFails] at intervalTotalCall
                      cases intervalTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.hcompPath`.  Like `pathApp`, the
endpoints are dispatcher-needed but not in source.  Take endpoint
strengthening witnesses as extra hypotheses. -/
theorem isAggregatorTotal_hcompPath_with_endpoints {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesPathTotal : IsAggregatorTotal sidesPath)
    (capTotal : IsAggregatorTotal capValue)
    (leftEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetLeftEndpoint,
          leftEndpoint.partialStrengthen? strengthening.back =
            some targetLeftEndpoint)
    (rightEndpointTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierType : Ty level targetScope},
        carrierType.partialStrengthen? strengthening.back =
            some targetCarrierType →
        ∃ targetRightEndpoint,
          rightEndpoint.partialStrengthen? strengthening.back =
            some targetRightEndpoint) :
    IsAggregatorTotal
      (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
        sidesPath capValue) := by
  intros _ _ strengthening targetCarrierType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (sidesPathRaw.partialStrengthen? strengthening.back)
      (capRaw.partialStrengthen? strengthening.back)
      RawTerm.hcomp = some _ at rawStrengthens
  obtain ⟨_, _, sidesPathRawSuccess, capRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetLeftEndpoint, leftEndpointSuccess⟩ :=
    leftEndpointTotal strengthening typeStrengthens
  obtain ⟨targetRightEndpoint, rightEndpointSuccess⟩ :=
    rightEndpointTotal strengthening typeStrengthens
  have pathTypeStrengthens :
      (Ty.path carrierType leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.path targetCarrierType targetLeftEndpoint
          targetRightEndpoint) := by
    show Option.mapThree
        (carrierType.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.path = _
    rw [typeStrengthens, leftEndpointSuccess, rightEndpointSuccess]
    rfl
  have sidesPathTotalCall :=
    sidesPathTotal strengthening pathTypeStrengthens sidesPathRawSuccess
  have capTotalCall :=
    capTotal strengthening typeStrengthens capRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [typeStrengthens] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftEndpointSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightEndpointSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next sidesPathFails =>
                  rw [sidesPathFails] at sidesPathTotalCall
                  cases sidesPathTotalCall
              · next _ _ =>
                  split
                  · next capFails =>
                      rw [capFails] at capTotalCall
                      cases capTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.glueElim`.  Source type is
`baseType`; dispatcher needs baseType.back + boundaryWitness.back +
gluedValue IH (type `Ty.glue baseType boundaryWitness`).  Take
boundaryWitness strengthening as extra hypothesis. -/
theorem isAggregatorTotal_glueElim_with_boundary {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {gluedValue :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedTotal : IsAggregatorTotal gluedValue)
    (boundaryTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetBaseType : Ty level targetScope},
        baseType.partialStrengthen? strengthening.back =
            some targetBaseType →
        ∃ targetBoundaryWitness,
          boundaryWitness.partialStrengthen? strengthening.back =
            some targetBoundaryWitness) :
    IsAggregatorTotal
      (Term.glueElim modeIsUnivalent gluedValue) := by
  intros _ _ strengthening targetBaseType _ typeStrengthens rawStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetGluedRaw gluedRawRenameSuccess =>
    have gluedRawSuccess :
        gluedRaw.partialStrengthen? strengthening.back =
          some targetGluedRaw := gluedRawRenameSuccess
    obtain ⟨targetBoundaryWitness, boundarySuccess⟩ :=
      boundaryTotal strengthening typeStrengthens
    have glueTypeStrengthens :
        (Ty.glue baseType boundaryWitness).partialStrengthen?
            strengthening.back =
          some (Ty.glue targetBaseType targetBoundaryWitness) := by
      show Option.mapTwo
          (baseType.partialStrengthen? strengthening.back)
          (boundaryWitness.partialStrengthen? strengthening.back)
          Ty.glue = _
      rw [typeStrengthens, boundarySuccess]
      rfl
    have gluedTotalCall :=
      gluedTotal strengthening glueTypeStrengthens gluedRawSuccess
    unfold partialStrengthenTyped?
    split
    · next baseFails =>
        rw [typeStrengthens] at baseFails
        cases baseFails
    · next _ _ =>
        split
        · next boundaryFails =>
            rw [boundarySuccess] at boundaryFails
            cases boundaryFails
        · next _ _ =>
            split
            · next gluedFails =>
                rw [gluedFails] at gluedTotalCall
                cases gluedTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.codataDest`.  Source type is
`outputType`; dispatcher needs stateType.back + outputType.back +
codataValue IH (type `Ty.codata stateType outputType`).  Take
stateType strengthening as extra hypothesis. -/
theorem isAggregatorTotal_codataDest_with_state {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataTotal : IsAggregatorTotal codataValue)
    (stateTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetOutputType : Ty level targetScope},
        outputType.partialStrengthen? strengthening.back =
            some targetOutputType →
        ∃ targetStateType,
          stateType.partialStrengthen? strengthening.back =
            some targetStateType) :
    IsAggregatorTotal (Term.codataDest codataValue) := by
  intros _ _ strengthening targetOutputType _ typeStrengthens rawStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetCodataRaw codataRawRenameSuccess =>
    have codataRawSuccess :
        codataRaw.partialStrengthen? strengthening.back =
          some targetCodataRaw := codataRawRenameSuccess
    obtain ⟨targetStateType, stateTypeSuccess⟩ :=
      stateTypeTotal strengthening typeStrengthens
    have codataTypeStrengthens :
        (Ty.codata stateType outputType).partialStrengthen?
            strengthening.back =
          some (Ty.codata targetStateType targetOutputType) := by
      show Option.mapTwo
          (stateType.partialStrengthen? strengthening.back)
          (outputType.partialStrengthen? strengthening.back)
          Ty.codata = _
      rw [stateTypeSuccess, typeStrengthens]
      rfl
    have codataTotalCall :=
      codataTotal strengthening codataTypeStrengthens codataRawSuccess
    unfold partialStrengthenTyped?
    split
    · next stateFails =>
        rw [stateTypeSuccess] at stateFails
        cases stateFails
    · next _ _ =>
        split
        · next outputFails =>
            rw [typeStrengthens] at outputFails
            cases outputFails
        · next _ _ =>
            split
            · next codataFails =>
                rw [codataFails] at codataTotalCall
                cases codataTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.fst`.  Source type is
`firstType`; dispatcher needs firstType.back + secondType.back.lift +
pairTerm IH (type `Ty.sigmaTy firstType secondType`).  Take
secondType.back.lift strengthening as extra hypothesis. -/
theorem isAggregatorTotal_fst_with_second {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairTotal : IsAggregatorTotal pairTerm)
    (secondTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetFirstType : Ty level targetScope},
        firstType.partialStrengthen? strengthening.back =
            some targetFirstType →
        ∃ targetSecondType,
          secondType.partialStrengthen? strengthening.back.lift =
            some targetSecondType) :
    IsAggregatorTotal (Term.fst pairTerm) := by
  intros _ _ strengthening targetFirstType _ typeStrengthens rawStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetPairRaw pairRawRenSuccess =>
    have pairRawSuccess :
        pairRaw.partialStrengthen? strengthening.back =
          some targetPairRaw := pairRawRenSuccess
    obtain ⟨targetSecondType, secondTypeSuccess⟩ :=
      secondTypeTotal strengthening typeStrengthens
    have sigmaTypeStrengthens :
        (Ty.sigmaTy firstType secondType).partialStrengthen?
            strengthening.back =
          some (Ty.sigmaTy targetFirstType targetSecondType) := by
      show Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = _
      rw [typeStrengthens, secondTypeSuccess]
      rfl
    have pairTotalCall :=
      pairTotal strengthening sigmaTypeStrengthens pairRawSuccess
    unfold partialStrengthenTyped?
    split
    · next firstFails =>
        rw [typeStrengthens] at firstFails
        cases firstFails
    · next _ _ =>
        split
        · next secondFails =>
            rw [secondTypeSuccess] at secondFails
            cases secondFails
        · next _ _ =>
            split
            · next pairFails =>
                rw [pairFails] at pairTotalCall
                cases pairTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.equivApp`.  Source type is
`carrierB`; dispatcher needs carrierA.back + carrierB.back +
equivTerm IH (Ty.equiv) + argumentTerm IH (carrierA).  Take
carrierA.back strengthening as extra hypothesis. -/
theorem isAggregatorTotal_equivApp_with_carrierA {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivTotal : IsAggregatorTotal equivTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (carrierATotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierB : Ty level targetScope},
        carrierB.partialStrengthen? strengthening.back =
            some targetCarrierB →
        ∃ targetCarrierA,
          carrierA.partialStrengthen? strengthening.back =
            some targetCarrierA) :
    IsAggregatorTotal (Term.equivApp equivTerm argumentTerm) := by
  intros _ _ strengthening targetCarrierB _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (equivRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.equivApp = some _ at rawStrengthens
  obtain ⟨_, _, equivRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrierA, carrierASuccess⟩ :=
    carrierATotal strengthening typeStrengthens
  have equivTypeStrengthens :
      (Ty.equiv carrierA carrierB).partialStrengthen?
          strengthening.back =
        some (Ty.equiv targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv = _
    rw [carrierASuccess, typeStrengthens]
    rfl
  have equivTotalCall :=
    equivTotal strengthening equivTypeStrengthens equivRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening carrierASuccess argumentRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [typeStrengthens] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next equivFails =>
              rw [equivFails] at equivTotalCall
              cases equivTotalCall
          · next _ _ =>
              split
              · next argumentFails =>
                  rw [argumentFails] at argumentTotalCall
                  cases argumentTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.equivApply`.  Like equivApp but
the raw uses RawTerm.equivApply.  Same auxiliary witness pattern. -/
theorem isAggregatorTotal_equivApply_with_carrierA {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    {equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term sourceCtx carrierA argumentRaw}
    (equivTotal : IsAggregatorTotal equivTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (carrierATotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierB : Ty level targetScope},
        carrierB.partialStrengthen? strengthening.back =
            some targetCarrierB →
        ∃ targetCarrierA,
          carrierA.partialStrengthen? strengthening.back =
            some targetCarrierA) :
    IsAggregatorTotal (Term.equivApply equivTerm argumentTerm) := by
  intros _ _ strengthening targetCarrierB _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (equivRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.equivApply = some _ at rawStrengthens
  obtain ⟨_, _, equivRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrierA, carrierASuccess⟩ :=
    carrierATotal strengthening typeStrengthens
  have equivTypeStrengthens :
      (Ty.equiv carrierA carrierB).partialStrengthen?
          strengthening.back =
        some (Ty.equiv targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv = _
    rw [carrierASuccess, typeStrengthens]
    rfl
  have equivTotalCall :=
    equivTotal strengthening equivTypeStrengthens equivRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening carrierASuccess argumentRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [typeStrengthens] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next equivFails =>
              rw [equivFails] at equivTotalCall
              cases equivTotalCall
          · next _ _ =>
              split
              · next argumentFails =>
                  rw [argumentFails] at argumentTotalCall
                  cases argumentTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.refineElim`.  Source type is
`baseType`; dispatcher needs baseType.back + predicate.back.lift +
refinedValue IH (type `Ty.refine baseType predicate`).  Take
predicate.back.lift strengthening as extra hypothesis. -/
theorem isAggregatorTotal_refineElim_with_predicate {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRaw : RawTerm sourceScope}
    {refinedValue :
      Term sourceCtx (Ty.refine baseType predicate) refinedRaw}
    (refinedTotal : IsAggregatorTotal refinedValue)
    (predicateTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetBaseType : Ty level targetScope},
        baseType.partialStrengthen? strengthening.back =
            some targetBaseType →
        ∃ targetPredicate,
          predicate.partialStrengthen? strengthening.back.lift =
            some targetPredicate) :
    IsAggregatorTotal (Term.refineElim refinedValue) := by
  intros _ _ strengthening targetBaseType _ typeStrengthens rawStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetRefinedRaw refinedRawRenSuccess =>
    have refinedRawSuccess :
        refinedRaw.partialStrengthen? strengthening.back =
          some targetRefinedRaw := refinedRawRenSuccess
    obtain ⟨targetPredicate, predicateSuccess⟩ :=
      predicateTotal strengthening typeStrengthens
    have refineTypeStrengthens :
        (Ty.refine baseType predicate).partialStrengthen?
            strengthening.back =
          some (Ty.refine targetBaseType targetPredicate) := by
      show Option.mapTwo
          (baseType.partialStrengthen? strengthening.back)
          (predicate.partialStrengthen? strengthening.back.lift)
          Ty.refine = _
      rw [typeStrengthens, predicateSuccess]
      rfl
    have refinedTotalCall :=
      refinedTotal strengthening refineTypeStrengthens refinedRawSuccess
    unfold partialStrengthenTyped?
    split
    · next baseFails =>
        rw [typeStrengthens] at baseFails
        cases baseFails
    · next _ _ =>
        split
        · next predicateFails =>
            rw [predicateSuccess] at predicateFails
            cases predicateFails
        · next _ _ =>
            split
            · next refinedFails =>
                rw [refinedFails] at refinedTotalCall
                cases refinedTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.app`.  Source type is
`codomainType`; dispatcher needs domainType.back + codomainType.back +
functionTerm IH (Ty.arrow) + argumentTerm IH (domainType).  Take
domainType.back strengthening as extra hypothesis. -/
theorem isAggregatorTotal_app_with_domain {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionTotal : IsAggregatorTotal functionTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (domainTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCodomainType : Ty level targetScope},
        codomainType.partialStrengthen? strengthening.back =
            some targetCodomainType →
        ∃ targetDomainType,
          domainType.partialStrengthen? strengthening.back =
            some targetDomainType) :
    IsAggregatorTotal (Term.app functionTerm argumentTerm) := by
  intros _ _ strengthening targetCodomainType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (functionRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.app = some _ at rawStrengthens
  obtain ⟨_, _, functionRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetDomainType, domainSuccess⟩ :=
    domainTotal strengthening typeStrengthens
  have arrowTypeStrengthens :
      (Ty.arrow domainType codomainType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetDomainType targetCodomainType) := by
    show Option.mapTwo
        (domainType.partialStrengthen? strengthening.back)
        (codomainType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [domainSuccess, typeStrengthens]
    rfl
  have functionTotalCall :=
    functionTotal strengthening arrowTypeStrengthens functionRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening domainSuccess argumentRawSuccess
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [typeStrengthens] at codomainFails
          cases codomainFails
      · next _ _ =>
          split
          · next functionFails =>
              rw [functionFails] at functionTotalCall
              cases functionTotalCall
          · next _ _ =>
              split
              · next argumentFails =>
                  rw [argumentFails] at argumentTotalCall
                  cases argumentTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.idJ`.  Source type is `motiveType`;
dispatcher needs carrier.back + leftEndpoint.back + rightEndpoint.back +
baseCase IH (motiveType) + witness IH (Ty.id carrier leftEndpoint
rightEndpoint).  Take the three Ty.id-component witnesses as extra
hypotheses. -/
theorem isAggregatorTotal_idJ_with_id_components {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseTotal : IsAggregatorTotal baseCase)
    (witnessTotal : IsAggregatorTotal witness)
    (idComponentsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetCarrier targetLeftEndpoint targetRightEndpoint,
          carrier.partialStrengthen? strengthening.back =
              some targetCarrier ∧
          leftEndpoint.partialStrengthen? strengthening.back =
              some targetLeftEndpoint ∧
          rightEndpoint.partialStrengthen? strengthening.back =
              some targetRightEndpoint) :
    IsAggregatorTotal (Term.idJ baseCase witness) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (witnessRaw.partialStrengthen? strengthening.back)
      RawTerm.idJ = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, witnessRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrier, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess⟩ :=
    idComponentsTotal strengthening typeStrengthens
  have idTypeStrengthens :
      (Ty.id carrier leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.id targetCarrier targetLeftEndpoint targetRightEndpoint) := by
    show Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.id = _
    rw [carrierSuccess, leftSuccess, rightSuccess]
    rfl
  have baseTotalCall :=
    baseTotal strengthening typeStrengthens baseRawSuccess
  have witnessTotalCall :=
    witnessTotal strengthening idTypeStrengthens witnessRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next baseFails =>
                  rw [baseFails] at baseTotalCall
                  cases baseTotalCall
              · next _ _ =>
                  split
                  · next witnessFails =>
                      rw [witnessFails] at witnessTotalCall
                      cases witnessTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.oeqJ`.  Same structure as idJ
but with Ty.oeq instead of Ty.id. -/
theorem isAggregatorTotal_oeqJ_with_oeq_components {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseTotal : IsAggregatorTotal baseCase)
    (witnessTotal : IsAggregatorTotal witness)
    (oeqComponentsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetCarrier targetLeftEndpoint targetRightEndpoint,
          carrier.partialStrengthen? strengthening.back =
              some targetCarrier ∧
          leftEndpoint.partialStrengthen? strengthening.back =
              some targetLeftEndpoint ∧
          rightEndpoint.partialStrengthen? strengthening.back =
              some targetRightEndpoint) :
    IsAggregatorTotal (Term.oeqJ baseCase witness) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (witnessRaw.partialStrengthen? strengthening.back)
      RawTerm.oeqJ = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, witnessRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrier, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess⟩ :=
    oeqComponentsTotal strengthening typeStrengthens
  have oeqTypeStrengthens :
      (Ty.oeq carrier leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.oeq targetCarrier targetLeftEndpoint targetRightEndpoint) := by
    show Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.oeq = _
    rw [carrierSuccess, leftSuccess, rightSuccess]
    rfl
  have baseTotalCall :=
    baseTotal strengthening typeStrengthens baseRawSuccess
  have witnessTotalCall :=
    witnessTotal strengthening oeqTypeStrengthens witnessRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next baseFails =>
                  rw [baseFails] at baseTotalCall
                  cases baseTotalCall
              · next _ _ =>
                  split
                  · next witnessFails =>
                      rw [witnessFails] at witnessTotalCall
                      cases witnessTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.idStrictRec`.  Source type is
`motiveType`; same structure as idJ/oeqJ with Ty.idStrict. -/
theorem isAggregatorTotal_idStrictRec_with_idStrict_components
    {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRaw witnessRaw : RawTerm sourceScope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseTotal : IsAggregatorTotal baseCase)
    (witnessTotal : IsAggregatorTotal witness)
    (idStrictComponentsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetCarrier targetLeftEndpoint targetRightEndpoint,
          carrier.partialStrengthen? strengthening.back =
              some targetCarrier ∧
          leftEndpoint.partialStrengthen? strengthening.back =
              some targetLeftEndpoint ∧
          rightEndpoint.partialStrengthen? strengthening.back =
              some targetRightEndpoint) :
    IsAggregatorTotal
      (Term.idStrictRec modeIsStrict baseCase witness) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (baseRaw.partialStrengthen? strengthening.back)
      (witnessRaw.partialStrengthen? strengthening.back)
      RawTerm.idStrictRec = some _ at rawStrengthens
  obtain ⟨_, _, baseRawSuccess, witnessRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrier, targetLeftEndpoint, targetRightEndpoint,
    carrierSuccess, leftSuccess, rightSuccess⟩ :=
    idStrictComponentsTotal strengthening typeStrengthens
  have idStrictTypeStrengthens :
      (Ty.idStrict carrier leftEndpoint rightEndpoint).partialStrengthen?
          strengthening.back =
        some (Ty.idStrict targetCarrier targetLeftEndpoint
          targetRightEndpoint) := by
    show Option.mapThree
        (carrier.partialStrengthen? strengthening.back)
        (leftEndpoint.partialStrengthen? strengthening.back)
        (rightEndpoint.partialStrengthen? strengthening.back)
        Ty.idStrict = _
    rw [carrierSuccess, leftSuccess, rightSuccess]
    rfl
  have baseTotalCall :=
    baseTotal strengthening typeStrengthens baseRawSuccess
  have witnessTotalCall :=
    witnessTotal strengthening idStrictTypeStrengthens witnessRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · next _ _ =>
              split
              · next baseFails =>
                  rw [baseFails] at baseTotalCall
                  cases baseTotalCall
              · next _ _ =>
                  split
                  · next witnessFails =>
                      rw [witnessFails] at witnessTotalCall
                      cases witnessTotalCall
                  · rfl

/-- Bridge totality wrapper for `Term.equivReflIdAtId`.  Source type
`Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw`
encodes carrierRaw but NOT carrier (Ty).  Take carrier.back as extra
hypothesis. -/
theorem isAggregatorTotal_equivReflIdAtId_with_carrier {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope)
    (carrierTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierRaw : RawTerm targetScope},
        carrierRaw.partialStrengthen? strengthening.back =
            some targetCarrierRaw →
        ∃ targetCarrier,
          carrier.partialStrengthen? strengthening.back =
            some targetCarrier) :
    IsAggregatorTotal
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel innerLevelLt
        carrier carrierRaw) := by
  intros _ _ strengthening _ _ typeStrengthens _
  change Option.mapThree
      ((Ty.universe innerLevel innerLevelLt :
          Ty level sourceScope).partialStrengthen?
        strengthening.back)
      (carrierRaw.partialStrengthen? strengthening.back)
      (carrierRaw.partialStrengthen? strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, _, _, _, carrierRawSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  obtain ⟨_, carrierSuccess⟩ :=
    carrierTotal strengthening carrierRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next carrierRawFails =>
          rw [carrierRawSuccess] at carrierRawFails
          cases carrierRawFails
      · rfl

/-- Bridge totality wrapper for `Term.uaToEquiv`.  Source type
`Ty.equiv leftTy rightTy` encodes the carrier Ty's but the dispatcher
also reads leftTyRaw / rightTyRaw (positional schematic raw fields).
Take them as extra hypotheses. -/
theorem isAggregatorTotal_uaToEquiv_with_carrier_raws {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    {proof : Term sourceCtx
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                     leftTyRaw rightTyRaw)
              proofRaw}
    (proofTotal : IsAggregatorTotal proof)
    (carrierRawsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetLeftTy targetRightTy : Ty level targetScope},
        leftTy.partialStrengthen? strengthening.back =
            some targetLeftTy →
        rightTy.partialStrengthen? strengthening.back =
            some targetRightTy →
        ∃ targetLeftTyRaw targetRightTyRaw,
          leftTyRaw.partialStrengthen? strengthening.back =
              some targetLeftTyRaw ∧
          rightTyRaw.partialStrengthen? strengthening.back =
              some targetRightTyRaw) :
    IsAggregatorTotal
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (leftTy.partialStrengthen? strengthening.back)
      (rightTy.partialStrengthen? strengthening.back)
      Ty.equiv = some _ at typeStrengthens
  obtain ⟨targetLeftTy, targetRightTy, leftTySuccess, rightTySuccess, _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens: (RawTerm.uaToEquiv proofRaw).back
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetProofRaw proofRawRenSuccess =>
    have proofRawSuccess :
        proofRaw.partialStrengthen? strengthening.back =
          some targetProofRaw := proofRawRenSuccess
    obtain ⟨targetLeftTyRaw, targetRightTyRaw, leftRawSuccess,
      rightRawSuccess⟩ :=
      carrierRawsTotal strengthening leftTySuccess rightTySuccess
    -- proof's type: Ty.id (Ty.universe ...) leftTyRaw rightTyRaw
    have universeStrengthens :
        (Ty.universe innerLevel innerLevelLt :
            Ty level sourceScope).partialStrengthen? strengthening.back =
          some (Ty.universe innerLevel innerLevelLt) := rfl
    have idTypeStrengthens :
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw
          ).partialStrengthen? strengthening.back =
          some (Ty.id (Ty.universe innerLevel innerLevelLt) targetLeftTyRaw
            targetRightTyRaw) := by
      show Option.mapThree
          ((Ty.universe innerLevel innerLevelLt :
              Ty level sourceScope).partialStrengthen?
            strengthening.back)
          (leftTyRaw.partialStrengthen? strengthening.back)
          (rightTyRaw.partialStrengthen? strengthening.back)
          Ty.id = _
      rw [universeStrengthens, leftRawSuccess, rightRawSuccess]
      rfl
    have proofTotalCall :=
      proofTotal strengthening idTypeStrengthens proofRawSuccess
    unfold partialStrengthenTyped?
    split
    · next leftTyFails =>
        rw [leftTySuccess] at leftTyFails
        cases leftTyFails
    · next _ _ =>
        split
        · next rightTyFails =>
            rw [rightTySuccess] at rightTyFails
            cases rightTyFails
        · next _ _ =>
            split
            · next leftRawFails =>
                rw [leftRawSuccess] at leftRawFails
                cases leftRawFails
            · next _ _ =>
                split
                · next rightRawFails =>
                    rw [rightRawSuccess] at rightRawFails
                    cases rightRawFails
                · next _ _ =>
                    split
                    · next proofFails =>
                        rw [proofFails] at proofTotalCall
                        cases proofTotalCall
                    · rfl

/-- Bridge totality wrapper for `Term.uaIntroHet`.  Source type
`Ty.id (Ty.universe...) carrierARaw carrierBRaw` encodes carrierARaw/
carrierBRaw via Ty.id mapThree but NOT carrierA/carrierB (Ty's).
Source raw `RawTerm.equivIntro forwardRaw backwardRaw` gives forwardRaw,
backwardRaw via mapTwo.  Take carrierA.back + carrierB.back as
extra hypotheses. -/
theorem isAggregatorTotal_uaIntroHet_with_carriers {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    {equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivTotal : IsAggregatorTotal equivWitness)
    (carrierTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierARaw targetCarrierBRaw : RawTerm targetScope},
        carrierARaw.partialStrengthen? strengthening.back =
            some targetCarrierARaw →
        carrierBRaw.partialStrengthen? strengthening.back =
            some targetCarrierBRaw →
        ∃ targetCarrierA targetCarrierB,
          carrierA.partialStrengthen? strengthening.back =
              some targetCarrierA ∧
          carrierB.partialStrengthen? strengthening.back =
              some targetCarrierB) :
    IsAggregatorTotal
      (Term.uaIntroHet (context := sourceCtx) innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens: Ty.id (Ty.universe ...) carrierARaw carrierBRaw
  change Option.mapThree
      ((Ty.universe innerLevel innerLevelLt :
          Ty level sourceScope).partialStrengthen?
        strengthening.back)
      (carrierARaw.partialStrengthen? strengthening.back)
      (carrierBRaw.partialStrengthen? strengthening.back)
      Ty.id = some _ at typeStrengthens
  obtain ⟨_, _, _, _, carrierARawSuccess, carrierBRawSuccess, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  -- rawStrengthens: RawTerm.equivIntro forwardRaw backwardRaw
  change Option.mapTwo
      (forwardRaw.partialStrengthen? strengthening.back)
      (backwardRaw.partialStrengthen? strengthening.back)
      RawTerm.equivIntro = some _ at rawStrengthens
  obtain ⟨targetForwardRaw, targetBackwardRaw, forwardRawSuccess,
    backwardRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetCarrierA, targetCarrierB, carrierASuccess,
    carrierBSuccess⟩ :=
    carrierTotal strengthening carrierARawSuccess carrierBRawSuccess
  -- equivWitness's type: Ty.equiv carrierA carrierB
  have equivTypeStrengthens :
      (Ty.equiv carrierA carrierB).partialStrengthen?
          strengthening.back =
        some (Ty.equiv targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.equiv = _
    rw [carrierASuccess, carrierBSuccess]
    rfl
  -- equivWitness's raw: RawTerm.equivIntro forwardRaw backwardRaw
  have equivRawStrengthens :
      (RawTerm.equivIntro forwardRaw backwardRaw).partialStrengthen?
          strengthening.back =
        some (RawTerm.equivIntro targetForwardRaw targetBackwardRaw) := by
    change Option.mapTwo
        (forwardRaw.partialStrengthen? strengthening.back)
        (backwardRaw.partialStrengthen? strengthening.back)
        RawTerm.equivIntro = _
    rw [forwardRawSuccess, backwardRawSuccess]
    rfl
  have equivTotalCall :=
    equivTotal strengthening equivTypeStrengthens equivRawStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [carrierBSuccess] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next carrierARawFails =>
              rw [carrierARawSuccess] at carrierARawFails
              cases carrierARawFails
          · next _ _ =>
              split
              · next carrierBRawFails =>
                  rw [carrierBRawSuccess] at carrierBRawFails
                  cases carrierBRawFails
              · next _ _ =>
                  split
                  · next forwardRawFails =>
                      rw [forwardRawSuccess] at forwardRawFails
                      cases forwardRawFails
                  · next _ _ =>
                      split
                      · next backwardRawFails =>
                          rw [backwardRawSuccess] at backwardRawFails
                          cases backwardRawFails
                      · next _ _ =>
                          split
                          · next equivFails =>
                              rw [equivFails] at equivTotalCall
                              cases equivTotalCall
                          · rfl

/-- Bridge totality wrapper for `Term.equivIntroHet`.  Source type
`Ty.equiv carrierA carrierB` encodes the carriers via mapTwo.  Source
raw `RawTerm.equivIntro forwardRaw backwardRaw` encodes those raws
but NOT leftInvRaw / rightInvRaw.  Take the missing raws as extra
hypotheses. -/
theorem isAggregatorTotal_equivIntroHet_with_inv_raws {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrierA carrierB : Ty level sourceScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {forward : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    (forwardTotal : IsAggregatorTotal forward)
    (backwardTotal : IsAggregatorTotal backward)
    (leftInvTotal : IsAggregatorTotal leftInv)
    (rightInvTotal : IsAggregatorTotal rightInv)
    (invRawsTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetCarrierA targetCarrierB : Ty level targetScope}
        {targetForwardRaw targetBackwardRaw : RawTerm targetScope},
        carrierA.partialStrengthen? strengthening.back =
            some targetCarrierA →
        carrierB.partialStrengthen? strengthening.back =
            some targetCarrierB →
        forwardRaw.partialStrengthen? strengthening.back =
            some targetForwardRaw →
        backwardRaw.partialStrengthen? strengthening.back =
            some targetBackwardRaw →
        ∃ targetLeftInvRaw targetRightInvRaw,
          leftInvRaw.partialStrengthen? strengthening.back =
              some targetLeftInvRaw ∧
          rightInvRaw.partialStrengthen? strengthening.back =
              some targetRightInvRaw) :
    IsAggregatorTotal
      (Term.equivIntroHet forward backward leftInv rightInv) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (carrierA.partialStrengthen? strengthening.back)
      (carrierB.partialStrengthen? strengthening.back)
      Ty.equiv = some _ at typeStrengthens
  obtain ⟨targetCarrierA, targetCarrierB, carrierASuccess, carrierBSuccess,
    _⟩ :=
    Option.mapTwo_eq_some typeStrengthens
  change Option.mapTwo
      (forwardRaw.partialStrengthen? strengthening.back)
      (backwardRaw.partialStrengthen? strengthening.back)
      RawTerm.equivIntro = some _ at rawStrengthens
  obtain ⟨targetForwardRaw, targetBackwardRaw, forwardRawSuccess,
    backwardRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetLeftInvRaw, targetRightInvRaw, leftInvRawSuccess,
    rightInvRawSuccess⟩ :=
    invRawsTotal strengthening carrierASuccess carrierBSuccess
      forwardRawSuccess backwardRawSuccess
  -- Forward IH: type Ty.arrow carrierA carrierB
  have forwardArrowStrengthens :
      (Ty.arrow carrierA carrierB).partialStrengthen? strengthening.back =
        some (Ty.arrow targetCarrierA targetCarrierB) := by
    show Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        (carrierB.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [carrierASuccess, carrierBSuccess]
    rfl
  have backwardArrowStrengthens :
      (Ty.arrow carrierB carrierA).partialStrengthen? strengthening.back =
        some (Ty.arrow targetCarrierB targetCarrierA) := by
    show Option.mapTwo
        (carrierB.partialStrengthen? strengthening.back)
        (carrierA.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [carrierASuccess, carrierBSuccess]
    rfl
  have forwardTotalCall :=
    forwardTotal strengthening forwardArrowStrengthens forwardRawSuccess
  have backwardTotalCall :=
    backwardTotal strengthening backwardArrowStrengthens backwardRawSuccess
  -- Aux weakens for inverse-law type strengthening
  have carrierAWeakenStrengthens :
      carrierA.weaken.partialStrengthen? strengthening.back.lift =
        some targetCarrierA.weaken := by
    rw [Ty.partialStrengthen?_weaken_lift carrierA strengthening.back,
      carrierASuccess]
    rfl
  have carrierBWeakenStrengthens :
      carrierB.weaken.partialStrengthen? strengthening.back.lift =
        some targetCarrierB.weaken := by
    rw [Ty.partialStrengthen?_weaken_lift carrierB strengthening.back,
      carrierBSuccess]
    rfl
  have forwardRawWeakenStrengthens :
      forwardRaw.weaken.partialStrengthen? strengthening.back.lift =
        some targetForwardRaw.weaken := by
    rw [RawTerm.partialStrengthen?_weaken_lift forwardRaw
      strengthening.back, forwardRawSuccess]
    rfl
  have backwardRawWeakenStrengthens :
      backwardRaw.weaken.partialStrengthen? strengthening.back.lift =
        some targetBackwardRaw.weaken := by
    rw [RawTerm.partialStrengthen?_weaken_lift backwardRaw
      strengthening.back, backwardRawSuccess]
    rfl
  -- LeftInv codomain reconstruction
  have leftAppForwardStrengthens :
      (RawTerm.app forwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetForwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
    change Option.mapTwo
        (forwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
        RawTerm.app = _
    rw [forwardRawWeakenStrengthens]
    rfl
  have leftAppBackForwardStrengthens :
      (RawTerm.app backwardRaw.weaken
          (RawTerm.app forwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetBackwardRaw.weaken
          (RawTerm.app targetForwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))) := by
    change Option.mapTwo
        (backwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app forwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift)
        RawTerm.app = _
    rw [backwardRawWeakenStrengthens, leftAppForwardStrengthens]
    rfl
  have leftInvCodomainStrengthens :
      (equivIntroHetLeftInverseCodomain carrierA forwardRaw
        backwardRaw).partialStrengthen? strengthening.back.lift =
        some (equivIntroHetLeftInverseCodomain targetCarrierA
          targetForwardRaw targetBackwardRaw) := by
    change Option.mapThree
        (carrierA.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app backwardRaw.weaken
          (RawTerm.app forwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift)
        ((RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩
          ).partialStrengthen? strengthening.back.lift)
        Ty.id = _
    rw [carrierAWeakenStrengthens, leftAppBackForwardStrengthens]
    rfl
  have leftInvTypeStrengthens :
      (equivIntroHetLeftInverseType carrierA forwardRaw
        backwardRaw).partialStrengthen? strengthening.back =
        some (equivIntroHetLeftInverseType targetCarrierA targetForwardRaw
          targetBackwardRaw) := by
    change Option.mapTwo
        (carrierA.partialStrengthen? strengthening.back)
        ((equivIntroHetLeftInverseCodomain carrierA forwardRaw
          backwardRaw).partialStrengthen? strengthening.back.lift)
        Ty.piTy = _
    rw [carrierASuccess, leftInvCodomainStrengthens]
    rfl
  -- RightInv similarly
  have rightAppBackwardStrengthens :
      (RawTerm.app backwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetBackwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) := by
    change Option.mapTwo
        (backwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        (some (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
        RawTerm.app = _
    rw [backwardRawWeakenStrengthens]
    rfl
  have rightAppForwardBackwardStrengthens :
      (RawTerm.app forwardRaw.weaken
          (RawTerm.app backwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift =
        some (RawTerm.app targetForwardRaw.weaken
          (RawTerm.app targetBackwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))) := by
    change Option.mapTwo
        (forwardRaw.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app backwardRaw.weaken
          (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)
          ).partialStrengthen? strengthening.back.lift)
        RawTerm.app = _
    rw [forwardRawWeakenStrengthens, rightAppBackwardStrengthens]
    rfl
  have rightInvCodomainStrengthens :
      (equivIntroHetRightInverseCodomain carrierB forwardRaw
        backwardRaw).partialStrengthen? strengthening.back.lift =
        some (equivIntroHetRightInverseCodomain targetCarrierB
          targetForwardRaw targetBackwardRaw) := by
    change Option.mapThree
        (carrierB.weaken.partialStrengthen? strengthening.back.lift)
        ((RawTerm.app forwardRaw.weaken
          (RawTerm.app backwardRaw.weaken
            (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
          ).partialStrengthen? strengthening.back.lift)
        ((RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩
          ).partialStrengthen? strengthening.back.lift)
        Ty.id = _
    rw [carrierBWeakenStrengthens, rightAppForwardBackwardStrengthens]
    rfl
  have rightInvTypeStrengthens :
      (equivIntroHetRightInverseType carrierB forwardRaw
        backwardRaw).partialStrengthen? strengthening.back =
        some (equivIntroHetRightInverseType targetCarrierB
          targetForwardRaw targetBackwardRaw) := by
    change Option.mapTwo
        (carrierB.partialStrengthen? strengthening.back)
        ((equivIntroHetRightInverseCodomain carrierB forwardRaw
          backwardRaw).partialStrengthen? strengthening.back.lift)
        Ty.piTy = _
    rw [carrierBSuccess, rightInvCodomainStrengthens]
    rfl
  have leftInvTotalCall :=
    leftInvTotal strengthening leftInvTypeStrengthens leftInvRawSuccess
  have rightInvTotalCall :=
    rightInvTotal strengthening rightInvTypeStrengthens rightInvRawSuccess
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · next _ _ =>
      split
      · next carrierBFails =>
          rw [carrierBSuccess] at carrierBFails
          cases carrierBFails
      · next _ _ =>
          split
          · next forwardFails =>
              rw [forwardFails] at forwardTotalCall
              cases forwardTotalCall
          · next _ _ =>
              split
              · next backwardFails =>
                  rw [backwardFails] at backwardTotalCall
                  cases backwardTotalCall
              · next _ _ =>
                  split
                  · next leftInvFails =>
                      rw [leftInvFails] at leftInvTotalCall
                      cases leftInvTotalCall
                  · next _ _ =>
                      split
                      · next rightInvFails =>
                          rw [rightInvFails] at rightInvTotalCall
                          cases rightInvTotalCall
                      · rfl

/-- Bridge totality wrapper for `Term.sessionSend`.  Source type is
`Ty.session protocolStep`; dispatcher needs protocolStep.back + channel
IH (Ty.session protocolStep) + payload IH (payloadType).  Take
payloadType.back as extra hypothesis (payloadType is NOT in source). -/
theorem isAggregatorTotal_sessionSend_with_payload {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelTotal : IsAggregatorTotal channel)
    (payloadTotal : IsAggregatorTotal payload)
    (payloadTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetProtocolStep : RawTerm targetScope},
        protocolStep.partialStrengthen? strengthening.back =
            some targetProtocolStep →
        ∃ targetPayloadType,
          payloadType.partialStrengthen? strengthening.back =
            some targetPayloadType) :
    IsAggregatorTotal
      (Term.sessionSend protocolStep channel payload) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens : (Ty.session protocolStep).back = some _
  -- Decompose by changing to the match form
  change (match protocolStep.partialStrengthen? strengthening.back with
          | some strengthenedProtocol => some (Ty.session strengthenedProtocol)
          | none => none) = some _ at typeStrengthens
  split at typeStrengthens
  rotate_left
  · cases typeStrengthens
  next targetProtocolStep protocolSuccess =>
    -- rawStrengthens : (RawTerm.sessionSend channelRaw payloadRaw).back
    change Option.mapTwo
        (channelRaw.partialStrengthen? strengthening.back)
        (payloadRaw.partialStrengthen? strengthening.back)
        RawTerm.sessionSend = some _ at rawStrengthens
    obtain ⟨_, _, channelRawSuccess, payloadRawSuccess, _⟩ :=
      Option.mapTwo_eq_some rawStrengthens
    obtain ⟨targetPayloadType, payloadTypeSuccess⟩ :=
      payloadTypeTotal strengthening protocolSuccess
    -- channel's type strengthens
    have sessionTypeStrengthens :
        (Ty.session (level := level) protocolStep).partialStrengthen?
            strengthening.back =
          some (Ty.session (level := level) targetProtocolStep) := by
      show (match protocolStep.partialStrengthen? strengthening.back with
          | some strengthenedProtocol =>
              some (Ty.session (level := level) strengthenedProtocol)
          | none => none) = _
      rw [protocolSuccess]
    have channelTotalCall :=
      channelTotal strengthening sessionTypeStrengthens channelRawSuccess
    have payloadTotalCall :=
      payloadTotal strengthening payloadTypeSuccess payloadRawSuccess
    unfold partialStrengthenTyped?
    split
    · next protocolFails =>
        rw [protocolSuccess] at protocolFails
        cases protocolFails
    · next _ _ =>
        split
        · next channelFails =>
            rw [channelFails] at channelTotalCall
            cases channelTotalCall
        · next _ _ =>
            split
            · next payloadFails =>
                rw [payloadFails] at payloadTotalCall
                cases payloadTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.boolElim`.  Source type is
`motiveType.subst0 Ty.bool scrutineeRaw`; dispatcher needs
motiveType.back.lift + scrutinee IH (Ty.bool) + thenBranch IH +
elseBranch IH.  Take motiveType.back.lift as extra hypothesis.
thenBranch / elseBranch type strengthenings constructed via
`Ty.partialStrengthen?_subst0_of_success`. -/
theorem isAggregatorTotal_boolElim_with_motive {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (thenTotal : IsAggregatorTotal thenBranch)
    (elseTotal : IsAggregatorTotal elseBranch)
    (motiveTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetSourceType : Ty level targetScope},
        (motiveType.subst0 Ty.bool scrutineeRaw).partialStrengthen?
            strengthening.back =
            some targetSourceType →
        ∃ targetMotiveType,
          motiveType.partialStrengthen? strengthening.back.lift =
            some targetMotiveType) :
    IsAggregatorTotal
      (Term.boolElim scrutinee thenBranch elseBranch) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (thenRaw.partialStrengthen? strengthening.back)
      (elseRaw.partialStrengthen? strengthening.back)
      RawTerm.boolElim = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, thenRawSuccess, elseRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetMotiveType, motiveSuccess⟩ :=
    motiveTotal strengthening typeStrengthens
  -- scrutinee's type Ty.bool is closed-atomic
  have boolStrengthens :
      (Ty.bool : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.bool := rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening boolStrengthens scrutineeRawSuccess
  -- thenBranch's type: motiveType.subst0 Ty.bool RawTerm.boolTrue
  have boolTrueStrengthens :
      (RawTerm.boolTrue : RawTerm sourceScope).partialStrengthen?
          strengthening.back =
        some RawTerm.boolTrue := rfl
  have boolFalseStrengthens :
      (RawTerm.boolFalse : RawTerm sourceScope).partialStrengthen?
          strengthening.back =
        some RawTerm.boolFalse := rfl
  have thenTypeStrengthens :
      (motiveType.subst0 Ty.bool RawTerm.boolTrue).partialStrengthen?
          strengthening.back =
        some (targetMotiveType.subst0 Ty.bool RawTerm.boolTrue) :=
    Ty.partialStrengthen?_subst0_of_success motiveType targetMotiveType
      Ty.bool Ty.bool RawTerm.boolTrue RawTerm.boolTrue
      strengthening.forward strengthening.back strengthening.injectsBack
      strengthening.back_forward motiveSuccess boolStrengthens
      boolTrueStrengthens
  have elseTypeStrengthens :
      (motiveType.subst0 Ty.bool RawTerm.boolFalse).partialStrengthen?
          strengthening.back =
        some (targetMotiveType.subst0 Ty.bool RawTerm.boolFalse) :=
    Ty.partialStrengthen?_subst0_of_success motiveType targetMotiveType
      Ty.bool Ty.bool RawTerm.boolFalse RawTerm.boolFalse
      strengthening.forward strengthening.back strengthening.injectsBack
      strengthening.back_forward motiveSuccess boolStrengthens
      boolFalseStrengthens
  have thenTotalCall :=
    thenTotal strengthening thenTypeStrengthens thenRawSuccess
  have elseTotalCall :=
    elseTotal strengthening elseTypeStrengthens elseRawSuccess
  unfold partialStrengthenTyped?
  split
  · next motiveFails =>
      rw [motiveSuccess] at motiveFails
      cases motiveFails
  · next _ _ =>
      split
      · next scrutineeFails =>
          rw [scrutineeFails] at scrutineeTotalCall
          cases scrutineeTotalCall
      · next _ _ =>
          split
          · next thenFails =>
              rw [thenFails] at thenTotalCall
              cases thenTotalCall
          · next _ _ =>
              split
              · next elseFails =>
                  rw [elseFails] at elseTotalCall
                  cases elseTotalCall
              · rfl

/-- 3-IH totality: `Term.natElim`.  Source type is `motiveType`
directly (✓).  Dispatcher takes only 3 IH recurses (no type witness
checks).  scrutinee : Ty.nat (closed-atomic), zeroBranch : motiveType,
succBranch : Ty.arrow Ty.nat motiveType.  Construct succ's arrow type
strengthens from typeStrengthens + Ty.nat trivial. -/
theorem isAggregatorTotal_natElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (zeroTotal : IsAggregatorTotal zeroBranch)
    (succTotal : IsAggregatorTotal succBranch) :
    IsAggregatorTotal (Term.natElim scrutinee zeroBranch succBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (zeroRaw.partialStrengthen? strengthening.back)
      (succRaw.partialStrengthen? strengthening.back)
      RawTerm.natElim = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, zeroRawSuccess, succRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  have natStrengthens :
      (Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.nat := rfl
  have arrowStrengthens :
      (Ty.arrow Ty.nat motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow Ty.nat targetMotiveType) := by
    show Option.mapTwo
        ((Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [natStrengthens, typeStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening natStrengthens scrutineeRawSuccess
  have zeroTotalCall :=
    zeroTotal strengthening typeStrengthens zeroRawSuccess
  have succTotalCall :=
    succTotal strengthening arrowStrengthens succRawSuccess
  unfold partialStrengthenTyped?
  split
  · next scrutineeFails =>
      rw [scrutineeFails] at scrutineeTotalCall
      cases scrutineeTotalCall
  · next _ _ =>
      split
      · next zeroFails =>
          rw [zeroFails] at zeroTotalCall
          cases zeroTotalCall
      · next _ _ =>
          split
          · next succFails =>
              rw [succFails] at succTotalCall
              cases succTotalCall
          · rfl

/-- 3-IH totality: `Term.natRec`.  Source type motiveType (✓).
Like natElim but succBranch's type is
`Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)`. -/
theorem isAggregatorTotal_natRec {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx
        (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (zeroTotal : IsAggregatorTotal zeroBranch)
    (succTotal : IsAggregatorTotal succBranch) :
    IsAggregatorTotal (Term.natRec scrutinee zeroBranch succBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (zeroRaw.partialStrengthen? strengthening.back)
      (succRaw.partialStrengthen? strengthening.back)
      RawTerm.natRec = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, zeroRawSuccess, succRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  have natStrengthens :
      (Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.nat := rfl
  have innerArrowStrengthens :
      (Ty.arrow motiveType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetMotiveType targetMotiveType) := by
    show Option.mapTwo
        (motiveType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [typeStrengthens]
    rfl
  have outerArrowStrengthens :
      (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)).partialStrengthen?
          strengthening.back =
        some (Ty.arrow Ty.nat (Ty.arrow targetMotiveType
          targetMotiveType)) := by
    show Option.mapTwo
        ((Ty.nat : Ty level sourceScope).partialStrengthen?
          strengthening.back)
        ((Ty.arrow motiveType motiveType).partialStrengthen?
          strengthening.back)
        Ty.arrow = _
    rw [natStrengthens, innerArrowStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening natStrengthens scrutineeRawSuccess
  have zeroTotalCall :=
    zeroTotal strengthening typeStrengthens zeroRawSuccess
  have succTotalCall :=
    succTotal strengthening outerArrowStrengthens succRawSuccess
  unfold partialStrengthenTyped?
  split
  · next scrutineeFails =>
      rw [scrutineeFails] at scrutineeTotalCall
      cases scrutineeTotalCall
  · next _ _ =>
      split
      · next zeroFails =>
          rw [zeroFails] at zeroTotalCall
          cases zeroTotalCall
      · next _ _ =>
          split
          · next succFails =>
              rw [succFails] at succTotalCall
              cases succTotalCall
          · rfl

/-- Bridge totality wrapper for `Term.listElim`.  Source type
motiveType (✓); dispatcher needs elementType.back + 3 IH children.
Take elementType.back as extra hypothesis. -/
theorem isAggregatorTotal_listElim_with_element {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx (Ty.arrow elementType
        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (nilTotal : IsAggregatorTotal nilBranch)
    (consTotal : IsAggregatorTotal consBranch)
    (elementTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetElementType,
          elementType.partialStrengthen? strengthening.back =
            some targetElementType) :
    IsAggregatorTotal
      (Term.listElim scrutinee nilBranch consBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (nilRaw.partialStrengthen? strengthening.back)
      (consRaw.partialStrengthen? strengthening.back)
      RawTerm.listElim = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, nilRawSuccess, consRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetElementType, elementSuccess⟩ :=
    elementTypeTotal strengthening typeStrengthens
  -- scrutinee type: Ty.listType elementType
  have listTypeStrengthens :
      (Ty.listType elementType).partialStrengthen?
          strengthening.back =
        some (Ty.listType targetElementType) := by
    show (match elementType.partialStrengthen? strengthening.back with
          | some r => some (Ty.listType r)
          | none => none) = _
    rw [elementSuccess]
  -- consBranch type: Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType)
  have innerArrowStrengthens :
      (Ty.arrow (Ty.listType elementType) motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow (Ty.listType targetElementType) targetMotiveType) := by
    show Option.mapTwo
        ((Ty.listType elementType).partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [listTypeStrengthens, typeStrengthens]
    rfl
  have outerArrowStrengthens :
      (Ty.arrow elementType
        (Ty.arrow (Ty.listType elementType) motiveType)).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetElementType
          (Ty.arrow (Ty.listType targetElementType)
            targetMotiveType)) := by
    show Option.mapTwo
        (elementType.partialStrengthen? strengthening.back)
        ((Ty.arrow (Ty.listType elementType) motiveType).partialStrengthen?
          strengthening.back)
        Ty.arrow = _
    rw [elementSuccess, innerArrowStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening listTypeStrengthens scrutineeRawSuccess
  have nilTotalCall :=
    nilTotal strengthening typeStrengthens nilRawSuccess
  have consTotalCall :=
    consTotal strengthening outerArrowStrengthens consRawSuccess
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      rw [elementSuccess] at elementFails
      cases elementFails
  · next _ _ =>
      split
      · next scrutineeFails =>
          rw [scrutineeFails] at scrutineeTotalCall
          cases scrutineeTotalCall
      · next _ _ =>
          split
          · next nilFails =>
              rw [nilFails] at nilTotalCall
              cases nilTotalCall
          · next _ _ =>
              split
              · next consFails =>
                  rw [consFails] at consTotalCall
                  cases consTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.optionMatch`.  Source type
motiveType (✓); dispatcher needs elementType.back + 3 IH children. -/
theorem isAggregatorTotal_optionMatch_with_element {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (noneTotal : IsAggregatorTotal noneBranch)
    (someTotal : IsAggregatorTotal someBranch)
    (elementTypeTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetElementType,
          elementType.partialStrengthen? strengthening.back =
            some targetElementType) :
    IsAggregatorTotal
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (noneRaw.partialStrengthen? strengthening.back)
      (someRaw.partialStrengthen? strengthening.back)
      RawTerm.optionMatch = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, noneRawSuccess, someRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetElementType, elementSuccess⟩ :=
    elementTypeTotal strengthening typeStrengthens
  have optionTypeStrengthens :
      (Ty.optionType elementType).partialStrengthen?
          strengthening.back =
        some (Ty.optionType targetElementType) := by
    show (match elementType.partialStrengthen? strengthening.back with
          | some r => some (Ty.optionType r)
          | none => none) = _
    rw [elementSuccess]
  have arrowStrengthens :
      (Ty.arrow elementType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetElementType targetMotiveType) := by
    show Option.mapTwo
        (elementType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [elementSuccess, typeStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening optionTypeStrengthens scrutineeRawSuccess
  have noneTotalCall :=
    noneTotal strengthening typeStrengthens noneRawSuccess
  have someTotalCall :=
    someTotal strengthening arrowStrengthens someRawSuccess
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      rw [elementSuccess] at elementFails
      cases elementFails
  · next _ _ =>
      split
      · next scrutineeFails =>
          rw [scrutineeFails] at scrutineeTotalCall
          cases scrutineeTotalCall
      · next _ _ =>
          split
          · next noneFails =>
              rw [noneFails] at noneTotalCall
              cases noneTotalCall
          · next _ _ =>
              split
              · next someFails =>
                  rw [someFails] at someTotalCall
                  cases someTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.eitherMatch`.  Source type
motiveType (✓); dispatcher needs leftType.back + rightType.back +
3 IH children. -/
theorem isAggregatorTotal_eitherMatch_with_lr_types {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeTotal : IsAggregatorTotal scrutinee)
    (leftTotal : IsAggregatorTotal leftBranch)
    (rightTotal : IsAggregatorTotal rightBranch)
    (lrTypesTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetMotiveType : Ty level targetScope},
        motiveType.partialStrengthen? strengthening.back =
            some targetMotiveType →
        ∃ targetLeftType targetRightType,
          leftType.partialStrengthen? strengthening.back =
              some targetLeftType ∧
          rightType.partialStrengthen? strengthening.back =
              some targetRightType) :
    IsAggregatorTotal
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  intros _ _ strengthening targetMotiveType _ typeStrengthens rawStrengthens
  change Option.mapThree
      (scrutineeRaw.partialStrengthen? strengthening.back)
      (leftRaw.partialStrengthen? strengthening.back)
      (rightRaw.partialStrengthen? strengthening.back)
      RawTerm.eitherMatch = some _ at rawStrengthens
  obtain ⟨_, _, _, scrutineeRawSuccess, leftRawSuccess, rightRawSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  obtain ⟨targetLeftType, targetRightType, leftTypeSuccess,
    rightTypeSuccess⟩ :=
    lrTypesTotal strengthening typeStrengthens
  have eitherTypeStrengthens :
      (Ty.eitherType leftType rightType).partialStrengthen?
          strengthening.back =
        some (Ty.eitherType targetLeftType targetRightType) := by
    show Option.mapTwo
        (leftType.partialStrengthen? strengthening.back)
        (rightType.partialStrengthen? strengthening.back)
        Ty.eitherType = _
    rw [leftTypeSuccess, rightTypeSuccess]
    rfl
  have leftArrowStrengthens :
      (Ty.arrow leftType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetLeftType targetMotiveType) := by
    show Option.mapTwo
        (leftType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [leftTypeSuccess, typeStrengthens]
    rfl
  have rightArrowStrengthens :
      (Ty.arrow rightType motiveType).partialStrengthen?
          strengthening.back =
        some (Ty.arrow targetRightType targetMotiveType) := by
    show Option.mapTwo
        (rightType.partialStrengthen? strengthening.back)
        (motiveType.partialStrengthen? strengthening.back)
        Ty.arrow = _
    rw [rightTypeSuccess, typeStrengthens]
    rfl
  have scrutineeTotalCall :=
    scrutineeTotal strengthening eitherTypeStrengthens scrutineeRawSuccess
  have leftTotalCall :=
    leftTotal strengthening leftArrowStrengthens leftRawSuccess
  have rightTotalCall :=
    rightTotal strengthening rightArrowStrengthens rightRawSuccess
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      rw [leftTypeSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightTypeSuccess] at rightFails
          cases rightFails
      · next _ _ =>
          split
          · next motiveFails =>
              rw [typeStrengthens] at motiveFails
              cases motiveFails
          · next _ _ =>
              split
              · next scrutineeFails =>
                  rw [scrutineeFails] at scrutineeTotalCall
                  cases scrutineeTotalCall
              · next _ _ =>
                  split
                  · next leftBFails =>
                      rw [leftBFails] at leftTotalCall
                      cases leftTotalCall
                  · next _ _ =>
                      split
                      · next rightBFails =>
                          rw [rightBFails] at rightTotalCall
                          cases rightTotalCall
                      · rfl

/-- Bridge totality wrapper for `Term.snd`.  Source type is
`secondType.subst0 firstType (RawTerm.fst pairRaw)`; dispatcher needs
firstType.back + secondType.back.lift + pairTerm IH (Ty.sigmaTy).
Take firstType.back + secondType.back.lift as extra hypotheses. -/
theorem isAggregatorTotal_snd_with_sigma_witnesses {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairTotal : IsAggregatorTotal pairTerm)
    (sigmaTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetSourceType : Ty level targetScope},
        (secondType.subst0 firstType
          (RawTerm.fst pairRaw)).partialStrengthen? strengthening.back =
            some targetSourceType →
        ∃ targetFirstType targetSecondType,
          firstType.partialStrengthen? strengthening.back =
              some targetFirstType ∧
          secondType.partialStrengthen? strengthening.back.lift =
              some targetSecondType) :
    IsAggregatorTotal (Term.snd pairTerm) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetPairRaw pairRawRenSuccess =>
    have pairRawSuccess :
        pairRaw.partialStrengthen? strengthening.back =
          some targetPairRaw := pairRawRenSuccess
    obtain ⟨targetFirstType, targetSecondType, firstSuccess,
      secondSuccess⟩ :=
      sigmaTotal strengthening typeStrengthens
    have sigmaTypeStrengthens :
        (Ty.sigmaTy firstType secondType).partialStrengthen?
            strengthening.back =
          some (Ty.sigmaTy targetFirstType targetSecondType) := by
      show Option.mapTwo
          (firstType.partialStrengthen? strengthening.back)
          (secondType.partialStrengthen? strengthening.back.lift)
          Ty.sigmaTy = _
      rw [firstSuccess, secondSuccess]
      rfl
    have pairTotalCall :=
      pairTotal strengthening sigmaTypeStrengthens pairRawSuccess
    unfold partialStrengthenTyped?
    split
    · next firstFails =>
        rw [firstSuccess] at firstFails
        cases firstFails
    · next _ _ =>
        split
        · next secondFails =>
            rw [secondSuccess] at secondFails
            cases secondFails
        · next _ _ =>
            split
            · next pairFails =>
                rw [pairFails] at pairTotalCall
                cases pairTotalCall
            · rfl

/-- Bridge totality wrapper for `Term.appPi`.  Source type is
`codomainType.subst0 domainType argumentRaw`; dispatcher needs
domainType.back + codomainType.back.lift + function IH (Ty.piTy) +
argument IH (domainType).  Take domain + codomain witnesses as
extra hypotheses. -/
theorem isAggregatorTotal_appPi_with_pi_witnesses {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionTotal : IsAggregatorTotal functionTerm)
    (argumentTotal : IsAggregatorTotal argumentTerm)
    (piTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetSourceType : Ty level targetScope},
        (codomainType.subst0 domainType argumentRaw).partialStrengthen?
            strengthening.back =
            some targetSourceType →
        ∃ targetDomainType targetCodomainType,
          domainType.partialStrengthen? strengthening.back =
              some targetDomainType ∧
          codomainType.partialStrengthen? strengthening.back.lift =
              some targetCodomainType) :
    IsAggregatorTotal (Term.appPi functionTerm argumentTerm) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (functionRaw.partialStrengthen? strengthening.back)
      (argumentRaw.partialStrengthen? strengthening.back)
      RawTerm.app = some _ at rawStrengthens
  obtain ⟨_, _, functionRawSuccess, argumentRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetDomainType, targetCodomainType, domainSuccess,
    codomainSuccess⟩ :=
    piTotal strengthening typeStrengthens
  -- functionTerm type: Ty.piTy domainType codomainType
  have piTypeStrengthens :
      (Ty.piTy domainType codomainType).partialStrengthen?
          strengthening.back =
        some (Ty.piTy targetDomainType targetCodomainType) := by
    show Option.mapTwo
        (domainType.partialStrengthen? strengthening.back)
        (codomainType.partialStrengthen? strengthening.back.lift)
        Ty.piTy = _
    rw [domainSuccess, codomainSuccess]
    rfl
  have functionTotalCall :=
    functionTotal strengthening piTypeStrengthens functionRawSuccess
  have argumentTotalCall :=
    argumentTotal strengthening domainSuccess argumentRawSuccess
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainSuccess] at codomainFails
          cases codomainFails
      · next _ _ =>
          split
          · next functionFails =>
              rw [functionFails] at functionTotalCall
              cases functionTotalCall
          · next _ _ =>
              split
              · next argumentFails =>
                  rw [argumentFails] at argumentTotalCall
                  cases argumentTotalCall
              · rfl

/-- Bridge totality wrapper for `Term.transp`.  Source type is
`targetType`; dispatcher needs sourceType.back + targetType.back +
sourceTypeRaw.back + targetTypeRaw.back + 2 IH children.  Take the
3 missing witnesses (sourceType, sourceTypeRaw, targetTypeRaw) as
extra hypotheses. -/
theorem isAggregatorTotal_transp_with_path_witnesses {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (pathTotal : IsAggregatorTotal typePath)
    (sourceTotal : IsAggregatorTotal sourceValue)
    (transpWitnessesTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetTargetType : Ty level targetScope},
        targetType.partialStrengthen? strengthening.back =
            some targetTargetType →
        ∃ targetSourceType targetSourceTypeRaw targetTargetTypeRaw,
          sourceType.partialStrengthen? strengthening.back =
              some targetSourceType ∧
          sourceTypeRaw.partialStrengthen? strengthening.back =
              some targetSourceTypeRaw ∧
          targetTypeRaw.partialStrengthen? strengthening.back =
              some targetTargetTypeRaw) :
    IsAggregatorTotal
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) := by
  intros _ _ strengthening targetTargetType _ typeStrengthens rawStrengthens
  change Option.mapTwo
      (pathRaw.partialStrengthen? strengthening.back)
      (sourceRaw.partialStrengthen? strengthening.back)
      RawTerm.transp = some _ at rawStrengthens
  obtain ⟨_, _, pathRawSuccess, sourceRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetSourceType, targetSourceTypeRaw, targetTargetTypeRaw,
    sourceTypeSuccess, sourceTypeRawSuccess, targetTypeRawSuccess⟩ :=
    transpWitnessesTotal strengthening typeStrengthens
  -- typePath's type: Ty.path (Ty.universe ...) sourceTypeRaw targetTypeRaw
  have universeStrengthens :
      (Ty.universe universeLevel universeLevelLt :
          Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some (Ty.universe universeLevel universeLevelLt) := rfl
  have pathTypeStrengthens :
      (Ty.path (Ty.universe universeLevel universeLevelLt)
        sourceTypeRaw targetTypeRaw).partialStrengthen?
          strengthening.back =
        some (Ty.path (Ty.universe universeLevel universeLevelLt)
          targetSourceTypeRaw targetTargetTypeRaw) := by
    show Option.mapThree
        ((Ty.universe universeLevel universeLevelLt :
            Ty level sourceScope).partialStrengthen?
          strengthening.back)
        (sourceTypeRaw.partialStrengthen? strengthening.back)
        (targetTypeRaw.partialStrengthen? strengthening.back)
        Ty.path = _
    rw [universeStrengthens, sourceTypeRawSuccess, targetTypeRawSuccess]
    rfl
  have pathTotalCall :=
    pathTotal strengthening pathTypeStrengthens pathRawSuccess
  have sourceTotalCall :=
    sourceTotal strengthening sourceTypeSuccess sourceRawSuccess
  unfold partialStrengthenTyped?
  split
  · next sourceTypeFails =>
      rw [sourceTypeSuccess] at sourceTypeFails
      cases sourceTypeFails
  · next _ _ =>
      split
      · next targetTypeFails =>
          rw [typeStrengthens] at targetTypeFails
          cases targetTypeFails
      · next _ _ =>
          split
          · next sourceTypeRawFails =>
              rw [sourceTypeRawSuccess] at sourceTypeRawFails
              cases sourceTypeRawFails
          · next _ _ =>
              split
              · next targetTypeRawFails =>
                  rw [targetTypeRawSuccess] at targetTypeRawFails
                  cases targetTypeRawFails
              · next _ _ =>
                  split
                  · next pathFails =>
                      rw [pathFails] at pathTotalCall
                      cases pathTotalCall
                  · next _ _ =>
                      split
                      · next sourceFails =>
                          rw [sourceFails] at sourceTotalCall
                          cases sourceTotalCall
                      · rfl

/-- Bridge totality wrapper for `Term.effectPerform`.  Source type is
`Ty.effect resultCarrier effectTag`; the dispatcher needs
`effectTag.back` + `argumentCarrier.back` + `resultCarrier.back` +
operationTag IH + arguments IH.  Decomposing the source-type
strengthening yields `effectTag.back` and `resultCarrier.back`
through `Option.mapTwo_eq_some`, but `argumentCarrier.back` is NOT
recoverable from `Ty.effect resultCarrier effectTag` alone — take
it as an explicit aux witness (parametric on strengthening). -/
theorem isAggregatorTotal_effectPerform_with_opsig_witness {mode : Mode}
    {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (effectTag : RawTerm sourceScope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationTotal : IsAggregatorTotal operationTag)
    (argumentsTotal : IsAggregatorTotal arguments)
    (argumentCarrierTotal :
      ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
        (strengthening : ContextStrengthening sourceCtx targetCtx)
        {targetEffectTag : RawTerm targetScope}
        {targetResultCarrier : Ty level targetScope},
        effectTag.partialStrengthen? strengthening.back =
            some targetEffectTag →
        operationSignature.resultCarrier.partialStrengthen?
            strengthening.back =
            some targetResultCarrier →
        ∃ targetArgumentCarrier,
          operationSignature.argumentCarrier.partialStrengthen?
              strengthening.back =
            some targetArgumentCarrier) :
    IsAggregatorTotal
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- typeStrengthens decomposes Ty.effect resultCarrier effectTag
  change Option.mapTwo
      (operationSignature.resultCarrier.partialStrengthen?
        strengthening.back)
      (effectTag.partialStrengthen? strengthening.back)
      Ty.effect = some _ at typeStrengthens
  obtain ⟨targetResultCarrier, targetEffectTag, resultCarrierSuccess,
    effectTagSuccess, _⟩ := Option.mapTwo_eq_some typeStrengthens
  -- rawStrengthens decomposes RawTerm.effectPerform operationRaw argumentsRaw
  change Option.mapTwo
      (operationRaw.partialStrengthen? strengthening.back)
      (argumentsRaw.partialStrengthen? strengthening.back)
      RawTerm.effectPerform = some _ at rawStrengthens
  obtain ⟨_, _, operationRawSuccess, argumentsRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  obtain ⟨targetArgumentCarrier, argumentCarrierSuccess⟩ :=
    argumentCarrierTotal strengthening effectTagSuccess
      resultCarrierSuccess
  -- operationTag's type: Ty.effect argumentCarrier effectTag
  have operationTagTypeStrengthens :
      (Ty.effect operationSignature.argumentCarrier effectTag).partialStrengthen?
          strengthening.back =
        some (Ty.effect targetArgumentCarrier targetEffectTag) := by
    show Option.mapTwo
        (operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back)
        (effectTag.partialStrengthen? strengthening.back)
        Ty.effect = _
    rw [argumentCarrierSuccess, effectTagSuccess]
    rfl
  have operationTotalCall :=
    operationTotal strengthening operationTagTypeStrengthens
      operationRawSuccess
  have argumentsTotalCall :=
    argumentsTotal strengthening argumentCarrierSuccess
      argumentsRawSuccess
  unfold partialStrengthenTyped?
  split
  · next effectTagFails =>
      rw [effectTagSuccess] at effectTagFails
      cases effectTagFails
  · next _ _ =>
      split
      · next argumentCarrierFails =>
          rw [argumentCarrierSuccess] at argumentCarrierFails
          cases argumentCarrierFails
      · next _ _ =>
          split
          · next resultCarrierFails =>
              rw [resultCarrierSuccess] at resultCarrierFails
              cases resultCarrierFails
          · next _ _ =>
              split
              · next operationFails =>
                  rw [operationFails] at operationTotalCall
                  cases operationTotalCall
              · next _ _ =>
                  split
                  · next argumentsFails =>
                      rw [argumentsFails] at argumentsTotalCall
                      cases argumentsTotalCall
                  · rfl

/-! ## Image theorem trio — weaken / strengthen invertibility

Three closure theorems on the image of `Term.weaken` under
`partialStrengthenTyped?`:

* `weaken_inv_of_strengthenTyped?_some` — right-inverse soundness:
  any successful strengthening produces a target whose forward-renamed
  form is heterogeneously equal to the source.  Direct corollary of
  the universal aggregator headline.
* `strengthenTyped?_some_of_weaken` — completeness on the weaken
  image: strengthening a `Term.weaken` source always succeeds.  Shipped
  later via `Term.unweaken?`-based totality.
* `weaken_image_iff_strengthenTyped?_some` — headline iff combining
  Steps 1 and 2.
-/

/-- Image Step 1 — right-inverse soundness for ANY successful
strengthening.  When `partialStrengthenTyped?` returns `some result`,
the recovered target's forward-renamed form is heterogeneously equal
to the source term.

The result is a direct corollary of the universal aggregator headline:
the per-arm dispatcher wrappers compose into
`isAggregatorSound_universal`, which when applied to a specific
strengthening/result pair yields the `StrengtheningSoundness` record
whose `termRenames` field is the desired HEq.

Consumed by Step 3 (`weaken_image_iff_strengthenTyped?_some`) and by
the Step.eta cascade SR proofs in Phase B+ per `extended-roadmap.md`
Day 32. -/
theorem weaken_inv_of_strengthenTyped?_some {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening sourceTerm)
    (success : partialStrengthenTyped? sourceTerm strengthening
        = some result) :
    HEq sourceTerm result.renamedTarget :=
  (isAggregatorSound_universal sourceTerm strengthening result success).termRenames

/-- Rename-image soundness for successful typed strengthening.

Any successful `partialStrengthenTyped?` result exposes a target-context
term whose forward rename is heterogeneously equal to the original
source-context term.  This is the forward, already-available half of the
planned T3 rename-image iff; the reverse direction still needs a
universal T1 dispatcher packaging over the 67 Eq-form and 11 HEq-form
rename-totality cases. -/
theorem rename_image_of_strengthenTyped?_some {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening sourceTerm)
    (success : partialStrengthenTyped? sourceTerm strengthening = some result) :
    ∃ (targetType : Ty level targetScope)
      (targetRaw : RawTerm targetScope)
      (targetTerm : Term targetCtx targetType targetRaw),
      HEq sourceTerm (Term.rename strengthening.toTermRenaming targetTerm) := by
  exact ⟨result.targetType, result.targetRaw, result.targetTerm,
    weaken_inv_of_strengthenTyped?_some strengthening result success⟩

/-! ## Rename-image success packaging

These lemmas package the strength-T1 exact dispatcher equations into
the `.isSome` shape needed by the T3 rename-image iff.  Eq-form T1
cases reduce directly; cast-wrapped HEq-form cases need a separate
bridge because the proof-bearing survival/cast matches are not
definitionally transparent to ordinary rewriting.
-/

private theorem option_isSome_of_eq_some
    {ResultType : Type} {resultOption : Option ResultType}
    {resultValue : ResultType}
    (resultEq : resultOption = some resultValue) :
    resultOption.isSome = true := by
  rw [resultEq]
  rfl

/-- T3 reverse-image bridge for the closed `Term.unit` case. -/
theorem strengthenTyped?_rename_isSome_unit
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.unit (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_unit forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the closed `Term.boolTrue` case. -/
theorem strengthenTyped?_rename_isSome_boolTrue
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.boolTrue (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_boolTrue forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the closed `Term.boolFalse` case. -/
theorem strengthenTyped?_rename_isSome_boolFalse
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.boolFalse (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_boolFalse forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the closed `Term.natZero` case. -/
theorem strengthenTyped?_rename_isSome_natZero
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.natZero (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_natZero forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the closed `Term.interval0` case. -/
theorem strengthenTyped?_rename_isSome_interval0
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.interval0 (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_interval0 forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the closed `Term.interval1` case. -/
theorem strengthenTyped?_rename_isSome_interval1
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.interval1 (context := sourceCtx)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_interval1 forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the parametric `Term.universeCode` case. -/
theorem strengthenTyped?_rename_isSome_universeCode
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.universeCode (context := sourceCtx) innerLevel outerLevel
            cumulOk levelLe))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_universeCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerLevel
      outerLevel cumulOk levelLe)

/-- T3 reverse-image bridge for the parametric `Term.listNil` case. -/
theorem strengthenTyped?_rename_isSome_listNil
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listNil (context := sourceCtx) (elementType := elementType)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_listNil forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the parametric `Term.optionNone` case. -/
theorem strengthenTyped?_rename_isSome_optionNone
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionNone (context := sourceCtx) (elementType := elementType)))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_optionNone forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the parametric `Term.equivReflId` case. -/
theorem strengthenTyped?_rename_isSome_equivReflId
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivReflId (context := sourceCtx) carrier))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_equivReflId forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the parametric `Term.refl` case. -/
theorem strengthenTyped?_rename_isSome_refl
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.refl (context := sourceCtx) carrier rawWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_refl forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the parametric `Term.oeqRefl` case. -/
theorem strengthenTyped?_rename_isSome_oeqRefl
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.oeqRefl (context := sourceCtx) carrier rawWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_oeqRefl forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the parametric `Term.idStrictRefl` case. -/
theorem strengthenTyped?_rename_isSome_idStrictRefl
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier
            rawWitness))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_idStrictRefl forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects)

/-- T3 reverse-image bridge for the `Term.equivReflIdAtId` case. -/
theorem strengthenTyped?_rename_isSome_equivReflIdAtId
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
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivReflIdAtId (context := sourceCtx) innerLevel innerLevelLt
            carrier carrierRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_equivReflIdAtId forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerLevel
      innerLevelLt)

/-- T3 reverse-image induction step for `Term.natSucc`. -/
theorem strengthenTyped?_rename_isSome_natSucc
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
    {predecessorRaw : RawTerm sourceScope}
    (predecessor : Term sourceCtx Ty.nat predecessorRaw)
    (predecessorIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming predecessor)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            predecessor)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.natSucc predecessor))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_natSucc forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects predecessor
      predecessorIH)

/-- T3 reverse-image induction step for `Term.intervalOpp`. -/
theorem strengthenTyped?_rename_isSome_intervalOpp
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
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalOpp innerValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_intervalOpp forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerValue innerIH)

/-- T3 reverse-image induction step for `Term.modIntro`. -/
theorem strengthenTyped?_rename_isSome_modIntro
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modIntro innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_modIntro forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerTerm innerIH)

/-- T3 reverse-image induction step for `Term.modElim`. -/
theorem strengthenTyped?_rename_isSome_modElim
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.modElim innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_modElim forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerTerm innerIH)

/-- T3 reverse-image induction step for `Term.subsume`. -/
theorem strengthenTyped?_rename_isSome_subsume
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
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    (innerTerm : Term sourceCtx innerType innerRaw)
    (innerIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming innerTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            innerTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.subsume innerTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_subsume forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects innerTerm innerIH)

/-- T3 reverse-image induction step for `Term.optionSome`. -/
theorem strengthenTyped?_rename_isSome_optionSome
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
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx elementType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.optionSome valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_optionSome forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects valueTerm valueIH)

/-- T3 reverse-image induction step for `Term.eitherInl`. -/
theorem strengthenTyped?_rename_isSome_eitherInl
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx leftType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInl (rightType := rightType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_eitherInl forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects valueTerm valueIH)

/-- T3 reverse-image induction step for `Term.eitherInr`. -/
theorem strengthenTyped?_rename_isSome_eitherInr
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
    {leftType rightType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    (valueTerm : Term sourceCtx rightType valueRaw)
    (valueIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming valueTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            valueTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherInr (leftType := leftType) valueTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_eitherInr forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects valueTerm valueIH)

/-- T3 reverse-image induction step for `Term.sessionRecv`. -/
theorem strengthenTyped?_rename_isSome_sessionRecv
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
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    (channel : Term sourceCtx (Ty.session protocolStep) channelRaw)
    (channelIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming channel)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            channel)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.sessionRecv channel))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_sessionRecv forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects channel channelIH)

/-- T3 reverse-image induction step for `Term.cumulUp`. -/
theorem strengthenTyped?_rename_isSome_cumulUp
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
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    (typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (codeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming typeCode)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            typeCode)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow
            levelLeHigh typeCode))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_cumulUp forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects lowerLevel
      higherLevel cumulMonotone levelLeLow levelLeHigh typeCode codeIH)

/-- T3 reverse-image induction step for `Term.recordProj`. -/
theorem strengthenTyped?_rename_isSome_recordProj
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
    {singleFieldType : Ty level sourceScope}
    {recordRaw : RawTerm sourceScope}
    (recordValue : Term sourceCtx (Ty.record singleFieldType) recordRaw)
    (recordIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming recordValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            recordValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordProj recordValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_recordProj forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects recordValue
      recordIH)

/-- T3 reverse-image induction step for `Term.codataDest`. -/
theorem strengthenTyped?_rename_isSome_codataDest
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
    {codataRaw : RawTerm sourceScope}
    (codataValue : Term sourceCtx (Ty.codata stateType outputType) codataRaw)
    (codataIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming codataValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            codataValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.codataDest codataValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_codataDest forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects codataValue
      codataIH)

/-- T3 reverse-image induction step for `Term.recordIntro`. -/
theorem strengthenTyped?_rename_isSome_recordIntro
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
    {singleFieldType : Ty level sourceScope}
    {firstRaw : RawTerm sourceScope}
    (firstField : Term sourceCtx singleFieldType firstRaw)
    (fieldIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming firstField)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            firstField)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.recordIntro firstField))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_recordIntro forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects firstField fieldIH)

/-- T3 reverse-image induction step for `Term.glueElim`. -/
theorem strengthenTyped?_rename_isSome_glueElim
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
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming gluedValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            gluedValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.glueElim modeIsUnivalent gluedValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_glueElim forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects modeIsUnivalent
      gluedValue gluedIH)

/-- T3 reverse-image induction step for `Term.listCons`. -/
theorem strengthenTyped?_rename_isSome_listCons
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
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    (headTerm : Term sourceCtx elementType headRaw)
    (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw)
    (headIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming headTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            headTerm))
    (tailIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming tailTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            tailTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.listCons headTerm tailTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_listCons forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects headTerm tailTerm
      headIH tailIH)

/-- T3 reverse-image induction step for `Term.natElim`. -/
theorem strengthenTyped?_rename_isSome_natElim
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
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (zeroIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            zeroBranch))
    (succIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            succBranch)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natElim scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_natElim forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects scrutinee
      zeroBranch succBranch scrutineeIH zeroIH succIH)

/-- T3 reverse-image induction step for `Term.natRec`. -/
theorem strengthenTyped?_rename_isSome_natRec
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
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx Ty.nat scrutineeRaw)
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (zeroIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming zeroBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            zeroBranch))
    (succIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming succBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            succBranch)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.natRec scrutinee zeroBranch succBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_natRec forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects scrutinee
      zeroBranch succBranch scrutineeIH zeroIH succIH)

/-- T3 reverse-image induction step for `Term.app`. -/
theorem strengthenTyped?_rename_isSome_app
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
    {functionRaw argumentRaw : RawTerm sourceScope}
    (functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term sourceCtx domainType argumentRaw)
    (functionIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming functionTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            functionTerm))
    (argumentIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming argumentTerm)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            argumentTerm)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.app functionTerm argumentTerm))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_app forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects functionTerm
      argumentTerm functionIH argumentIH)

/-- T3 reverse-image induction step for `Term.listElim`. -/
theorem strengthenTyped?_rename_isSome_listElim
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
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRaw consRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term sourceCtx motiveType nilRaw)
    (consBranch :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (nilIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming nilBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            nilBranch))
    (consIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming consBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            consBranch)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listElim scrutinee nilBranch consBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_listElim forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects scrutinee
      nilBranch consBranch scrutineeIH nilIH consIH)

/-- T3 reverse-image induction step for `Term.optionMatch`. -/
theorem strengthenTyped?_rename_isSome_optionMatch
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
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRaw someRaw : RawTerm sourceScope}
    (scrutinee : Term sourceCtx (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term sourceCtx motiveType noneRaw)
    (someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (noneIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming noneBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            noneBranch))
    (someIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming someBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            someBranch)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionMatch scrutinee noneBranch someBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_optionMatch forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects scrutinee
      noneBranch someBranch scrutineeIH noneIH someIH)

/-- T3 reverse-image induction step for `Term.eitherMatch`. -/
theorem strengthenTyped?_rename_isSome_eitherMatch
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
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw leftRaw rightRaw : RawTerm sourceScope}
    (scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming scrutinee)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            scrutinee))
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftBranch))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightBranch)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightBranch)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherMatch scrutinee leftBranch rightBranch))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_eitherMatch forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects scrutinee
      leftBranch rightBranch scrutineeIH leftIH rightIH)

/-- T3 reverse-image induction step for `Term.intervalMeet`. -/
theorem strengthenTyped?_rename_isSome_intervalMeet
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
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftValue))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalMeet leftValue rightValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_intervalMeet forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects leftValue
      rightValue leftIH rightIH)

/-- T3 reverse-image induction step for `Term.intervalJoin`. -/
theorem strengthenTyped?_rename_isSome_intervalJoin
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
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    (leftIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming leftValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            leftValue))
    (rightIH :
      partialStrengthenTyped?
          (Term.rename typedRenaming rightValue)
          (ContextStrengthening.ofRenaming forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects)
        = some (StrengtheningResult.fromRename forwardRename typedRenaming
            renameInverse renameInverseLeft renameInverseInjects
            rightValue)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming (Term.intervalJoin leftValue rightValue))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_intervalJoin forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects leftValue
      rightValue leftIH rightIH)

/-- T3 reverse-image seed for `Term.listCode`. -/
theorem strengthenTyped?_rename_isSome_listCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.listCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_listCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      elementCodeRaw)

/-- T3 reverse-image seed for `Term.optionCode`. -/
theorem strengthenTyped?_rename_isSome_optionCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.optionCode (context := sourceCtx) outerLevel levelLe
            elementCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_optionCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      elementCodeRaw)

/-- T3 reverse-image seed for `Term.arrowCode`. -/
theorem strengthenTyped?_rename_isSome_arrowCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.arrowCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_arrowCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      domainCodeRaw codomainCodeRaw)

/-- T3 reverse-image seed for `Term.sumCode`. -/
theorem strengthenTyped?_rename_isSome_sumCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sumCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_sumCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      leftCodeRaw rightCodeRaw)

/-- T3 reverse-image seed for `Term.productCode`. -/
theorem strengthenTyped?_rename_isSome_productCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.productCode (context := sourceCtx) outerLevel levelLe
            firstCodeRaw secondCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_productCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      firstCodeRaw secondCodeRaw)

/-- T3 reverse-image seed for `Term.eitherCode`. -/
theorem strengthenTyped?_rename_isSome_eitherCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.eitherCode (context := sourceCtx) outerLevel levelLe
            leftCodeRaw rightCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_eitherCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      leftCodeRaw rightCodeRaw)

/-- T3 reverse-image seed for `Term.idCode`. -/
theorem strengthenTyped?_rename_isSome_idCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.idCode (context := sourceCtx) outerLevel levelLe
            typeCodeRaw leftRaw rightRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_idCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      typeCodeRaw leftRaw rightRaw)

/-- T3 reverse-image seed for `Term.equivCode`. -/
theorem strengthenTyped?_rename_isSome_equivCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.equivCode (context := sourceCtx) outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_equivCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      leftTypeCodeRaw rightTypeCodeRaw)

/-- T3 reverse-image seed for `Term.piTyCode`. -/
theorem strengthenTyped?_rename_isSome_piTyCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.piTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_piTyCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      domainCodeRaw codomainCodeRaw)

/-- T3 reverse-image seed for `Term.sigmaTyCode`. -/
theorem strengthenTyped?_rename_isSome_sigmaTyCode
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
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    (partialStrengthenTyped?
        (Term.rename typedRenaming
          (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
            domainCodeRaw codomainCodeRaw))
        (ContextStrengthening.ofRenaming forwardRename typedRenaming
          renameInverse renameInverseLeft renameInverseInjects)).isSome =
      true :=
  option_isSome_of_eq_some
    (strengthenTyped?_rename_eq_sigmaTyCode forwardRename typedRenaming
      renameInverse renameInverseLeft renameInverseInjects outerLevel levelLe
      domainCodeRaw codomainCodeRaw)

/-- Image Step 2 — `unweaken?` and `strengthenTyped?` agree on success.

TAUTOLOGICAL BIJECTION: `Term.unweaken?` is defined to pattern-match on
`strengthenTyped?` and return `none` in the `none` branch.  Both
witnesses therefore succeed under identical conditions; this theorem
packages the equivalence as a one-line corollary and reveals no new
totality information.

If `Term.unweaken? weakenedTerm` returned `some originalTerm`, the
underlying `strengthenTyped?` dispatcher returned `some result`.  The
proof is case analysis on `strengthenTyped? weakenedTerm`: the `none`
branch makes `unweaken?` return `none`, contradicting the success
hypothesis. -/
theorem strengthenTyped?_some_of_unweaken?_some {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {weakenedTerm :
      Term (context.cons newType) sourceType.weaken sourceRaw.weaken}
    {originalTerm : Term context sourceType sourceRaw}
    (unweakSuccess : Term.unweaken? weakenedTerm = some originalTerm) :
    ∃ result, strengthenTyped? weakenedTerm = some result := by
  cases dispatchOutcome : strengthenTyped? weakenedTerm with
  | none =>
      exfalso
      have noneEq : Term.unweaken? weakenedTerm = none := by
        show (match strengthenTyped? weakenedTerm with
              | none => none
              | some result => _) = none
        rw [dispatchOutcome]
      rw [noneEq] at unweakSuccess
      cases unweakSuccess
  | some result =>
      exact ⟨result, rfl⟩

/-- Image Step 3 — headline iff between `unweaken?` success and
`strengthenTyped?` success.

TAUTOLOGICAL BIJECTION: both directions are structural corollaries of
`Term.unweaken?`'s definition (it pattern-matches on `strengthenTyped?`
and returns `none` exactly when `strengthenTyped?` does).  The iff
therefore reveals no new totality content — both witnesses succeed
under identical conditions, and the headline just packages that.

For a typed term whose indices are syntactic weakenings (the canonical
input shape consumed by the typed η-redesign + Phase B+ Step.eta SR
cascade), `Term.unweaken?` recovers an original-context term IFF the
underlying `strengthenTyped?` dispatcher produces a
`StrengtheningResult`.

NOTE: unconditional totality on the weakening image — i.e., `∀
originalTerm, strengthenTyped? (Term.weaken nt originalTerm) = some _`
— is a STRONGER theorem requiring a 78-case structural induction at the
typed Term layer (parallel to `Ty.partialStrengthen?_rename_some` and
`RawTerm.partialStrengthen?_rename_some`).  The structural induction
unifies the dispatcher pattern matches with the index-level
strengthen-of-weaken lemmas across every ctor with binder-lift
threading; tracked as a follow-up after this iff packaging lands. -/
theorem weaken_image_iff_strengthenTyped?_some {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (weakenedTerm :
      Term (context.cons newType) sourceType.weaken sourceRaw.weaken) :
    (∃ originalTerm, Term.unweaken? weakenedTerm = some originalTerm) ↔
      ∃ result, strengthenTyped? weakenedTerm = some result := by
  refine ⟨fun forwardHypothesis => ?_, fun backwardHypothesis => ?_⟩
  · obtain ⟨_, unweakSuccess⟩ := forwardHypothesis
    exact strengthenTyped?_some_of_unweaken?_some unweakSuccess
  · obtain ⟨result, dispatchSuccess⟩ := backwardHypothesis
    cases result with
    | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens _ _ =>
        have targetTypeEq : targetType = sourceType := by
          have hh : sourceType.weaken.strengthen? = some targetType :=
            typeStrengthens
          rw [Ty.strengthen?_weaken] at hh
          cases hh
          rfl
        have targetRawEq : targetRaw = sourceRaw := by
          have hh : sourceRaw.weaken.strengthen? = some targetRaw :=
            rawStrengthens
          rw [RawTerm.strengthen?_weaken] at hh
          cases hh
          rfl
        cases targetTypeEq
        cases targetRawEq
        refine ⟨targetTerm, ?_⟩
        show (match strengthenTyped? weakenedTerm with
              | none => none
              | some result => _) = some targetTerm
        rw [dispatchSuccess]

/-! ## `Term.weaken_inv_arrow` — conditional existence form (Phase A close-out)

The full existence-form companion to
`Term.weaken_inv_arrow_option` (Term/TypedInversion.lean).  Packages
the soundness component of `Term.unweaken?` as an existence-form
theorem: given a weakened arrow-typed term `weakenedFn` together with
an `unweaken?`-success witness producing the original `originalFn`,
the weakened term IS heterogeneously equal to `Term.weaken newType
originalFn`.

### Architecture rationale

The Step.eta plan's spec sketches an unconditional existence form `∀
arrowTerm, ∃ origArrowTerm, arrowTerm = origArrowTerm.weaken newType`,
but that is architecturally unshippable under the current
strengthening predicate (per Phase Y close-out commit `bdd613ec`): 25
of 78 Term constructors carry sub-types whose strengthening witness
is not recoverable from the source type's structure, so a universal
`IsAggregatorTotal` headline is impossible.

The conditional existence form below threads soundness through the
already-shipped image theorem
`weaken_inv_of_strengthenTyped?_some`, extracting the canonical
`HEq weakenedFn (Term.weaken newType originalFn)` from a
`Term.unweaken?` success.  Consumers (Phase B `lift_lam`
eta-disjunct) supply the `unweaken?` success themselves from their
own structural information about the typed app shape's function
side.

### Mechanical content

1. From `Term.unweaken? weakenedFn = some originalFn` infer
   `strengthenTyped? weakenedFn = some result` for some result
   with `result.targetTerm = originalFn` (after the indices are
   cast through `Ty.strengthen?_weaken` / `RawTerm.strengthen?_weaken`).
2. Apply `weaken_inv_of_strengthenTyped?_some` to get
   `HEq weakenedFn result.renamedTarget`.
3. Observe that `renamedTarget` is `Term.rename
   strengthening.toTermRenaming result.targetTerm`, and for
   `strengthening = dropNewest`, `toTermRenaming =
   TermRenaming.weakenStep` by `rfl`
   (`ContextStrengthening.dropNewest_toTermRenaming`).
4. Conclude `HEq weakenedFn (Term.weaken newType originalFn)` via
   the `@[reducible]` definition of `Term.weaken`.

### Phase B usage

The `lift_lam` η-disjunct receives an eta-shaped raw step `RawStep.
par (RawTerm.lam (RawTerm.app fnRaw.weaken (RawTerm.var 0)))
targetRaw`.  The typed body decomposes via `app_inv` into a function
term `fnTerm` at type `(Ty.arrow domainType codomainType).weaken`
over raw `fnRaw.weaken`.  Phase B will call `Term.unweaken?` on
`fnTerm`, refuting the `none` case via the structural reasoning that
the η raw shape forces, then invoke this theorem to obtain the typed
`origFn` plus the soundness HEq. -/

/-- **Conditional existence-form weaken inversion at arrow type.**

Given an arrow-typed weakened function term plus an `unweaken?`
success witness producing the original function term, conclude that
the weakened term is heterogeneously equal to the canonical
`Term.weaken newType originalFn`.

The `HEq` rather than `Eq` is necessary because the two sides have
indices

* `weakenedFn` : `Term (context.cons newType) (Ty.arrow domainType
  codomainType).weaken fnRaw.weaken`
* `Term.weaken newType originalFn` : same indices definitionally

but the indices are computed through different paths (the
`@[reducible]` `Term.weaken` wrapper vs the raw renaming path
inside `renamedTarget`).  `HEq` accepts the propositional-equal
indices uniformly. -/
theorem weaken_inv_arrow {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {domainType codomainType : Ty level scope}
    {fnRaw : RawTerm scope}
    (weakenedFn :
      Term (context.cons newType)
           (Ty.arrow domainType codomainType).weaken
           fnRaw.weaken)
    {originalFn : Term context (Ty.arrow domainType codomainType) fnRaw}
    (unweakenSuccess :
      Term.unweaken? weakenedFn = some originalFn) :
    HEq weakenedFn (Term.weaken newType originalFn) := by
  -- Step 1: unpack the `unweaken?` success into a `strengthenTyped?`
  -- success.  `Term.unweaken?` is defined by pattern-matching on
  -- `strengthenTyped?`; in the `some result` arm it casts the result
  -- target indices through `Ty.strengthen?_weaken` /
  -- `RawTerm.strengthen?_weaken` and produces `some result.targetTerm`.
  cases dispatchOutcome : strengthenTyped? weakenedFn with
  | none =>
      -- `unweaken?`'s `none` arm makes `unweakenSuccess` impossible.
      exfalso
      have noneEq : Term.unweaken? weakenedFn = none := by
        unfold Term.unweaken?
        rw [dispatchOutcome]
      rw [noneEq] at unweakenSuccess
      cases unweakenSuccess
  | some dispatchResult =>
      -- Apply the soundness headline FIRST (before destructuring) to
      -- extract the canonical `HEq weakenedFn
      -- dispatchResult.renamedTarget`.
      have soundness :
          HEq weakenedFn dispatchResult.renamedTarget :=
        weaken_inv_of_strengthenTyped?_some
          (ContextStrengthening.dropNewest context newType)
          dispatchResult dispatchOutcome
      -- Bridge `dispatchResult.renamedTarget` to `Term.weaken newType
      -- originalFn` by destructuring the result and identifying the
      -- canonical indices via `Ty.strengthen?_weaken` /
      -- `RawTerm.strengthen?_weaken`, then identifying `targetTerm`
      -- with `originalFn` from the `unweaken?` success.
      cases dispatchResult with
      | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
            typeRenames rawRenames =>
          -- Recover `targetType = Ty.arrow domainType codomainType`.
          have targetTypeEq :
              targetType = Ty.arrow domainType codomainType := by
            have rewritten :
                (Ty.arrow domainType codomainType).weaken.strengthen?
                  = some targetType := typeStrengthens
            rw [Ty.strengthen?_weaken (Ty.arrow domainType codomainType)]
              at rewritten
            injection rewritten with strengthenSomeEq
            exact strengthenSomeEq.symm
          -- Recover `targetRaw = fnRaw`.
          have targetRawEq : targetRaw = fnRaw := by
            have rewritten :
                fnRaw.weaken.strengthen? = some targetRaw :=
              rawStrengthens
            rw [RawTerm.strengthen?_weaken fnRaw] at rewritten
            injection rewritten with strengthenSomeEq
            exact strengthenSomeEq.symm
          subst targetTypeEq
          subst targetRawEq
          -- After the substitutions, `unweaken?` unfolds to
          -- `some targetTerm`, so `targetTerm = originalFn`.
          have unfoldEq :
              Term.unweaken? weakenedFn = some targetTerm := by
            unfold Term.unweaken?
            rw [dispatchOutcome]
          rw [unfoldEq] at unweakenSuccess
          injection unweakenSuccess with targetTermInj
          subst targetTermInj
          -- `soundness` is now `HEq weakenedFn renamedTarget` with
          -- `renamedTarget = Term.rename (dropNewest ...).toTermRenaming
          -- originalFn`.  By `dropNewest_toTermRenaming` (rfl) this is
          -- `Term.rename (TermRenaming.weakenStep ...) originalFn`,
          -- which is `Term.weaken newType originalFn` by the
          -- `@[reducible]` wrapper definition.
          exact soundness

/-! ## Closed-atomic unweaken? totality

The headline `Term.unweaken?_weaken : ∀ originalTerm newType,
  Term.unweaken? (Term.weaken newType originalTerm) = some originalTerm`
is the universal totality theorem on the weakening image.  A full
78-case structural induction proving it is mechanical — atomic ctors
reduce by `rfl`; recursive ctors compose via the per-ctor strengthening
builders and an `IsTotalOnWeaken` predicate.

This section ships the **closed-atomic foundation**: every ctor whose
typed `Term.weaken`-of-self reduces to a syntactic `Term.<ctor>` with
no per-ctor data carried at the surface (no element type, no codomain,
no payload).  Each such case is a one-line `rfl` because:

* `Term.weaken nt (Term.<ctor>) = Term.<ctor>` definitionally — `Term.rename`
  on a 0-arg ctor reduces directly.
* `partialStrengthenTyped? (Term.<ctor>)` is the dispatcher's closed-atomic
  arm, returning a concrete `StrengtheningResult` built from
  `partialStrengthenTyped<Ctor>` whose body is trivial.
* `unweaken?` matches that success and the type/raw alignment via
  `Ty.strengthen?_weaken` / `RawTerm.strengthen?_weaken` resolves to
  `Term.<ctor>` again.

The 7 ctors covered: `Term.unit`, `Term.boolTrue`, `Term.boolFalse`,
`Term.natZero`, `Term.interval0`, `Term.interval1`, plus `Term.var`
whose `Fin.succ position` shape exhibits the same structural success.

Each theorem here is a CONCRETE totality witness — not a universal
headline — and is consumable directly by Step.eta-cascade subject
reduction proofs whose source-side term is one of these atomic
constructors.  The remaining 71 recursive ctors land in follow-up
phases using the `IsTotalOnWeaken` predicate (Term-level totality
counterpart to `RawTerm.usesNewestSlot?` at the raw layer). -/

/-- Total-on-weaken predicate: a typed term whose weakening under any
new binder allows the typed strengthening dispatcher to succeed.  The
universal headline `∀ sourceTerm, IsTotalOnWeaken sourceTerm` is
provable by structural induction with 78 per-ctor cases; this file
ships the predicate plus the closed-atomic base cases. -/
def IsTotalOnWeaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw) : Prop :=
  ∀ (newType : Ty level scope),
    (strengthenTyped? (Term.weaken newType sourceTerm)).isSome

/-- Cast-invariance helper: `strengthenTyped?.isSome` is invariant under
a propositional cast on the Term's `Ty` index.

This is the load-bearing helper for totality proofs of the 7
Eq.mpr-blocked ctors (appPi, snd, pair, boolElim, funextRefl,
equivIntroHet, oeqFunext): their `Term.weaken` arm produces a term
wrapped in `Eq.mpr h _` due to `Ty.subst0_rename_commute.symm ▸ ...`,
which blocks pattern-matching in the strengthening dispatcher.  This
lemma reduces the cast term's `.isSome` to the un-cast form by
discharging the equation via `cases h`.

The motive is implicit: `fun (T : Ty level (scope+1)) => Term ctx T R`
where `R` is fixed (since `weaken`'s raw-side computation has no cast). -/
theorem strengthenTyped?_isSome_castInvariant
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {sourceTypeA sourceTypeB : Ty level (scope + 1)}
    {sourceRaw : RawTerm (scope + 1)}
    (sourceTerm : Term (context.cons newType) sourceTypeA sourceRaw)
    (typeEq : sourceTypeA = sourceTypeB) :
    (typeEq ▸ sourceTerm).strengthenTyped?.isSome =
      sourceTerm.strengthenTyped?.isSome := by
  cases typeEq
  rfl

/-- Closed-atomic totality: `Term.unit` strengthens through any
weakening.  Direct `rfl`-witness. -/
theorem isTotalOnWeaken_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.unit (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.boolTrue`. -/
theorem isTotalOnWeaken_boolTrue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.boolTrue (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.boolFalse`. -/
theorem isTotalOnWeaken_boolFalse {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.boolFalse (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.natZero`. -/
theorem isTotalOnWeaken_natZero {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.natZero (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.interval0`. -/
theorem isTotalOnWeaken_interval0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.interval0 (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.interval1`. -/
theorem isTotalOnWeaken_interval1 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    IsTotalOnWeaken (Term.interval1 (context := context)) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.var`.  The variable's renaming under
weakening lands at `Fin.succ position` which survives `dropNewest`
back to `position`. -/
theorem isTotalOnWeaken_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} (position : Fin scope) :
    IsTotalOnWeaken (Term.var (context := context) position) := by
  intro _; rfl

/-- Closed-atomic totality: `Term.universeCode`.  The universe-code
ctor carries pure value-level data (`innerLevel`, `outerLevel`,
`cumulOk`, `levelLe`) — no scope-indexed payload to strengthen, so the
dispatcher's arm succeeds unconditionally and totality is direct. -/
theorem isTotalOnWeaken_universeCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsTotalOnWeaken (Term.universeCode (context := context) innerLevel
      outerLevel cumulOk levelLe) := by
  intro _; rfl

/-- 1-IH non-binder totality: `Term.natSucc` is total on weaken if its
predecessor is.  Composition pattern shipped here as the canonical
template; the remaining 14 single-IH non-binder ctors (optionSome,
modIntro/Elim, subsume, eitherInl/Inr, recordIntro/Proj, refineElim,
fst, snd, intervalOpp, codataDest, sessionRecv) follow the same
unfold + split + ▸ pattern, landing per follow-up. -/
theorem isTotalOnWeaken_natSucc {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    {predecessor : Term context Ty.nat predecessorRaw}
    (predecessorIH : IsTotalOnWeaken predecessor) :
    IsTotalOnWeaken (Term.natSucc predecessor) := by
  intro newType
  show (strengthenTyped? (Term.natSucc (Term.weaken newType predecessor))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next predRecurse =>
      exfalso
      have totHyp := predecessorIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType predecessor))) = true :=
        predRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.intervalOpp`.  Cubical interval
negation; sibling of `natSucc` at a different carrier type. -/
theorem isTotalOnWeaken_intervalOpp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {pointRaw : RawTerm scope}
    {point : Term context Ty.interval pointRaw}
    (pointIH : IsTotalOnWeaken point) :
    IsTotalOnWeaken (Term.intervalOpp point) := by
  intro newType
  show (strengthenTyped? (Term.intervalOpp (Term.weaken newType point))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next pointRecurse =>
      exfalso
      have totHyp := pointIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType point))) = true :=
        pointRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.optionSome`.  Option-some carries
exactly one typed payload (the wrapped value); no Ty payload to
strengthen separately. -/
theorem isTotalOnWeaken_optionSome {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term context elementType valueRaw}
    (valueIH : IsTotalOnWeaken valueTerm) :
    IsTotalOnWeaken (Term.optionSome valueTerm) := by
  intro newType
  show (strengthenTyped? (Term.optionSome (Term.weaken newType valueTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next valueRecurse =>
      exfalso
      have totHyp := valueIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType valueTerm))) = true :=
        valueRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.modIntro`.  Modal introduction;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_modIntro {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.modIntro innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.modIntro (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.modElim`.  Modal elimination;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_modElim {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.modElim innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.modElim (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.subsume`.  Mode subsumption;
carries exactly one typed payload. -/
theorem isTotalOnWeaken_subsume {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIH : IsTotalOnWeaken innerTerm) :
    IsTotalOnWeaken (Term.subsume innerTerm) := by
  intro newType
  show (strengthenTyped? (Term.subsume (Term.weaken newType innerTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next innerRecurse =>
      exfalso
      have totHyp := innerIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType innerTerm))) = true :=
        innerRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.cumulUp`.  Cross-level cumulativity;
carries exactly one typed payload (the source type code).  No Ty payload
to strengthen separately — the universe levels are pure Nat data. -/
theorem isTotalOnWeaken_cumulUp {mode : Mode}
    {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeIH : IsTotalOnWeaken typeCode) :
    IsTotalOnWeaken (Term.cumulUp lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh typeCode) := by
  intro newType
  show (strengthenTyped? (Term.cumulUp lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh (Term.weaken newType typeCode))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next codeRecurse =>
      exfalso
      have totHyp := codeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType typeCode))) = true :=
        codeRecurse ▸ totHyp
      cases this
  · rfl

/-! ## Wave A: parametric atomic 0-IH totality

These ctors have no Term IH but carry one or more `Ty`/`RawTerm`
sub-payloads whose strengthening succeeds via `Ty.strengthen?_weaken`
or `RawTerm.strengthen?_weaken`.  The dispatcher's arm tests
`payload.partialStrengthen? strengthening.back`; under
`ContextStrengthening.dropNewest`, that is exactly `payload.weaken.strengthen?`
which always returns `some payload`.

Each proof follows the same shape: unfold the dispatcher, split on
the payload-strengthen success (the only `none` branch is impossible
because the payload here is `payload.weaken`), and discharge with
`rfl` after the success branch reduces. -/

/-- 0-IH parametric atomic totality: `Term.listNil`.  Element type
strengthens via `Ty.strengthen?_weaken`. -/
theorem isTotalOnWeaken_listNil {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    IsTotalOnWeaken (Term.listNil (context := context)
      (elementType := elementType)) := by
  intro newType
  show (strengthenTyped? (Term.listNil (context := context.cons newType)
      (elementType := elementType.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.optionNone`. -/
theorem isTotalOnWeaken_optionNone {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    IsTotalOnWeaken (Term.optionNone (context := context)
      (elementType := elementType)) := by
  intro newType
  show (strengthenTyped? (Term.optionNone (context := context.cons newType)
      (elementType := elementType.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.refl`.  Carries an explicit
Ty carrier + a raw witness, both at the outer scope.  Both strengthen
via `Ty.strengthen?_weaken` / `RawTerm.strengthen?_weaken`. -/
theorem isTotalOnWeaken_refl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    IsTotalOnWeaken (Term.refl (context := context) carrier rawWitness) := by
  intro newType
  show (strengthenTyped? (Term.refl (context := context.cons newType)
      (carrier.weaken) (rawWitness.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next witnessFails =>
        exfalso
        have witnessSuccess :
            rawWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rawWitness :=
          RawTerm.strengthen?_weaken rawWitness
        rw [witnessSuccess] at witnessFails
        cases witnessFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.oeqRefl`.  Same shape as
`refl` — carrier (Ty) + rawWitness (RawTerm). -/
theorem isTotalOnWeaken_oeqRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    IsTotalOnWeaken (Term.oeqRefl (context := context) carrier rawWitness) := by
  intro newType
  show (strengthenTyped? (Term.oeqRefl (context := context.cons newType)
      (carrier.weaken) (rawWitness.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next witnessFails =>
        exfalso
        have witnessSuccess :
            rawWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rawWitness :=
          RawTerm.strengthen?_weaken rawWitness
        rw [witnessSuccess] at witnessFails
        cases witnessFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.idStrictRefl`.  Same shape
as `refl` plus a `modeIsStrict` value-level parameter. -/
theorem isTotalOnWeaken_idStrictRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    IsTotalOnWeaken (Term.idStrictRefl (context := context)
      modeIsStrict carrier rawWitness) := by
  intro newType
  show (strengthenTyped? (Term.idStrictRefl
      (context := context.cons newType) modeIsStrict
      (carrier.weaken) (rawWitness.weaken))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next witnessFails =>
        exfalso
        have witnessSuccess :
            rawWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rawWitness :=
          RawTerm.strengthen?_weaken rawWitness
        rw [witnessSuccess] at witnessFails
        cases witnessFails
    · rfl

/-! ## Wave B: 1-IH non-binder totality (single Term recursion).

These ctors combine one Term IH with zero or more Ty/RawTerm
sub-payloads.  Each proof: split first on the payload-strengthen
successes (discharge `none` impossibilities via
`Ty.strengthen?_weaken`/`RawTerm.strengthen?_weaken`), then on the
recursive Term success (discharge `none` via the IH), then close
with `rfl`. -/

/-- 1-IH non-binder totality: `Term.recordIntro`.  Pure 1-IH ctor
(no extra Ty/RawTerm payload).  Same template as `natSucc`. -/
theorem isTotalOnWeaken_recordIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (fieldIH : IsTotalOnWeaken firstField) :
    IsTotalOnWeaken (Term.recordIntro firstField) := by
  intro newType
  show (strengthenTyped? (Term.recordIntro (Term.weaken newType
      firstField))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next fieldRecurse =>
      exfalso
      have totHyp := fieldIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType firstField))) = true :=
        fieldRecurse ▸ totHyp
      cases this
  · rfl

/-- 1-IH non-binder totality: `Term.recordProj`.  Carries one Ty
payload (singleFieldType) + one Term IH. -/
theorem isTotalOnWeaken_recordProj {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordIH : IsTotalOnWeaken recordValue) :
    IsTotalOnWeaken (Term.recordProj recordValue) := by
  intro newType
  show (strengthenTyped? (Term.recordProj (Term.weaken newType
      recordValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next fieldFails =>
      exfalso
      have fieldSuccess :
          singleFieldType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some singleFieldType :=
        Ty.strengthen?_weaken singleFieldType
      rw [fieldSuccess] at fieldFails
      cases fieldFails
  · split
    · next recordRecurse =>
        exfalso
        have totHyp := recordIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType recordValue))) = true :=
          recordRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.eitherInl`.  Carries one Ty
payload (rightType) + one Term IH. -/
theorem isTotalOnWeaken_eitherInl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term context leftType valueRaw}
    (valueIH : IsTotalOnWeaken valueTerm) :
    IsTotalOnWeaken (Term.eitherInl (rightType := rightType) valueTerm) := by
  intro newType
  show (strengthenTyped? (Term.eitherInl
      (rightType := rightType.weaken)
      (Term.weaken newType valueTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next rightFails =>
      exfalso
      have rightSuccess :
          rightType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some rightType :=
        Ty.strengthen?_weaken rightType
      rw [rightSuccess] at rightFails
      cases rightFails
  · split
    · next valueRecurse =>
        exfalso
        have totHyp := valueIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType valueTerm))) = true :=
          valueRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.eitherInr`.  Carries one Ty
payload (leftType) + one Term IH. -/
theorem isTotalOnWeaken_eitherInr {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term context rightType valueRaw}
    (valueIH : IsTotalOnWeaken valueTerm) :
    IsTotalOnWeaken (Term.eitherInr (leftType := leftType) valueTerm) := by
  intro newType
  show (strengthenTyped? (Term.eitherInr
      (leftType := leftType.weaken)
      (Term.weaken newType valueTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftType :=
        Ty.strengthen?_weaken leftType
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next valueRecurse =>
        exfalso
        have totHyp := valueIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType valueTerm))) = true :=
          valueRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.sessionRecv`.  Carries one RawTerm
payload (protocolStep) + one Term IH. -/
theorem isTotalOnWeaken_sessionRecv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term context (Ty.session protocolStep) channelRaw}
    (channelIH : IsTotalOnWeaken channel) :
    IsTotalOnWeaken (Term.sessionRecv channel) := by
  intro newType
  show (strengthenTyped? (Term.sessionRecv (Term.weaken newType
      channel))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next protocolFails =>
      exfalso
      have protocolSuccess :
          protocolStep.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some protocolStep :=
        RawTerm.strengthen?_weaken protocolStep
      rw [protocolSuccess] at protocolFails
      cases protocolFails
  · split
    · next channelRecurse =>
        exfalso
        have totHyp := channelIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType channel))) = true :=
          channelRecurse ▸ totHyp
        cases this
    · rfl

/-- 1-IH non-binder totality: `Term.codataDest`.  Carries two Ty
payloads (stateType, outputType) + one Term IH. -/
theorem isTotalOnWeaken_codataDest {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue : Term context (Ty.codata stateType outputType) codataRaw}
    (codataIH : IsTotalOnWeaken codataValue) :
    IsTotalOnWeaken (Term.codataDest codataValue) := by
  intro newType
  show (strengthenTyped? (Term.codataDest (Term.weaken newType
      codataValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next stateFails =>
      exfalso
      have stateSuccess :
          stateType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some stateType :=
        Ty.strengthen?_weaken stateType
      rw [stateSuccess] at stateFails
      cases stateFails
  · split
    · next outputFails =>
        exfalso
        have outputSuccess :
            outputType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some outputType :=
          Ty.strengthen?_weaken outputType
        rw [outputSuccess] at outputFails
        cases outputFails
    · split
      · next codataRecurse =>
          exfalso
          have totHyp := codataIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType codataValue))) = true :=
            codataRecurse ▸ totHyp
          cases this
      · rfl

/-! ## Wave C: 2-IH and 3-IH non-binder totality. -/

/-- 2-IH non-binder totality: `Term.listCons`.  Pure 2-IH ctor — no
extra Ty/RawTerm payloads. -/
theorem isTotalOnWeaken_listCons {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term context elementType headRaw}
    {tailTerm : Term context (Ty.listType elementType) tailRaw}
    (headIH : IsTotalOnWeaken headTerm)
    (tailIH : IsTotalOnWeaken tailTerm) :
    IsTotalOnWeaken (Term.listCons headTerm tailTerm) := by
  intro newType
  show (strengthenTyped? (Term.listCons (Term.weaken newType headTerm)
      (Term.weaken newType tailTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next headRecurse =>
      exfalso
      have totHyp := headIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType headTerm))) = true :=
        headRecurse ▸ totHyp
      cases this
  · split
    · next tailRecurse =>
        exfalso
        have totHyp := tailIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType tailTerm))) = true :=
          tailRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.intervalMeet`.  Pure 2-IH cubical
interval meet operator. -/
theorem isTotalOnWeaken_intervalMeet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftIH : IsTotalOnWeaken leftValue)
    (rightIH : IsTotalOnWeaken rightValue) :
    IsTotalOnWeaken (Term.intervalMeet leftValue rightValue) := by
  intro newType
  show (strengthenTyped? (Term.intervalMeet
      (Term.weaken newType leftValue)
      (Term.weaken newType rightValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftRecurse =>
      exfalso
      have totHyp := leftIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType leftValue))) = true :=
        leftRecurse ▸ totHyp
      cases this
  · split
    · next rightRecurse =>
        exfalso
        have totHyp := rightIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType rightValue))) = true :=
          rightRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.intervalJoin`.  Pure 2-IH cubical
interval join operator. -/
theorem isTotalOnWeaken_intervalJoin {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term context Ty.interval leftRaw}
    {rightValue : Term context Ty.interval rightRaw}
    (leftIH : IsTotalOnWeaken leftValue)
    (rightIH : IsTotalOnWeaken rightValue) :
    IsTotalOnWeaken (Term.intervalJoin leftValue rightValue) := by
  intro newType
  show (strengthenTyped? (Term.intervalJoin
      (Term.weaken newType leftValue)
      (Term.weaken newType rightValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftRecurse =>
      exfalso
      have totHyp := leftIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType leftValue))) = true :=
        leftRecurse ▸ totHyp
      cases this
  · split
    · next rightRecurse =>
        exfalso
        have totHyp := rightIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType rightValue))) = true :=
          rightRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.app`.  Carries two Ty payloads
(domainType, codomainType) + two Term IH (function, argument). -/
theorem isTotalOnWeaken_app {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm : Term context (Ty.arrow domainType codomainType)
      functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIH : IsTotalOnWeaken functionTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.app functionTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.app (Term.weaken newType functionTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next functionRecurse =>
          exfalso
          have totHyp := functionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType functionTerm))) = true :=
            functionRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.codataUnfold`.  One Ty (outputType)
+ two Term IH (initialState, transition).  Note: the dispatcher
strengthens only outputType (stateType is inferred from the IH). -/
theorem isTotalOnWeaken_codataUnfold {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term context stateType stateRaw}
    {transition : Term context (Ty.arrow stateType outputType)
      transitionRaw}
    (stateIH : IsTotalOnWeaken initialState)
    (transitionIH : IsTotalOnWeaken transition) :
    IsTotalOnWeaken (Term.codataUnfold initialState transition) := by
  intro newType
  show (strengthenTyped? (Term.codataUnfold
      (Term.weaken newType initialState)
      (Term.weaken newType transition))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next outputFails =>
      exfalso
      have outputSuccess :
          outputType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some outputType :=
        Ty.strengthen?_weaken outputType
      rw [outputSuccess] at outputFails
      cases outputFails
  · split
    · next stateRecurse =>
        exfalso
        have totHyp := stateIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType initialState))) = true :=
          stateRecurse ▸ totHyp
        cases this
    · split
      · next transitionRecurse =>
          exfalso
          have totHyp := transitionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType transition))) = true :=
            transitionRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.sessionSend`.  One RawTerm
(protocolStep) + one Ty (payloadType) + two Term IH. -/
theorem isTotalOnWeaken_sessionSend {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term context (Ty.session protocolStep) channelRaw}
    {payload : Term context payloadType payloadRaw}
    (channelIH : IsTotalOnWeaken channel)
    (payloadIH : IsTotalOnWeaken payload) :
    IsTotalOnWeaken (Term.sessionSend protocolStep channel payload) := by
  intro newType
  show (strengthenTyped? (Term.sessionSend protocolStep.weaken
      (Term.weaken newType channel)
      (Term.weaken newType payload))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next protocolFails =>
      exfalso
      have protocolSuccess :
          protocolStep.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some protocolStep :=
        RawTerm.strengthen?_weaken protocolStep
      rw [protocolSuccess] at protocolFails
      cases protocolFails
  · split
    · next channelRecurse =>
        exfalso
        have totHyp := channelIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType channel))) = true :=
          channelRecurse ▸ totHyp
        cases this
    · split
      · next payloadRecurse =>
          exfalso
          have totHyp := payloadIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType payload))) = true :=
            payloadRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.equivApp`.  Two Ty payloads
(carrierA, carrierB) + two Term IH (equiv, argument). -/
theorem isTotalOnWeaken_equivApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIH : IsTotalOnWeaken equivTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.equivApp equivTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.equivApp
      (Term.weaken newType equivTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next equivRecurse =>
          exfalso
          have totHyp := equivIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType equivTerm))) = true :=
            equivRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.equivApply`.  Same shape as
`equivApp` — two Ty payloads + two Term IH. -/
theorem isTotalOnWeaken_equivApply {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIH : IsTotalOnWeaken equivTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.equivApply equivTerm argumentTerm) := by
  intro newType
  show (strengthenTyped? (Term.equivApply
      (Term.weaken newType equivTerm)
      (Term.weaken newType argumentTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next equivRecurse =>
          exfalso
          have totHyp := equivIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType equivTerm))) = true :=
            equivRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.idJ`.  One Ty (carrier) + two
RawTerm (leftEndpoint, rightEndpoint) + two Term IH (baseCase,
witness). -/
theorem isTotalOnWeaken_idJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context (Ty.id carrier leftEndpoint rightEndpoint)
      witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.idJ baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.idJ (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.oeqJ`.  Same shape as `idJ`. -/
theorem isTotalOnWeaken_oeqJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
      witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.oeqJ baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.oeqJ (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.idStrictRec`.  Same shape as `idJ`
plus a `modeIsStrict` value-level parameter. -/
theorem isTotalOnWeaken_idStrictRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term context motiveType baseRaw}
    {witness : Term context
      (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseIH : IsTotalOnWeaken baseCase)
    (witnessIH : IsTotalOnWeaken witness) :
    IsTotalOnWeaken (Term.idStrictRec modeIsStrict baseCase witness) := by
  intro newType
  show (strengthenTyped? (Term.idStrictRec modeIsStrict
      (Term.weaken newType baseCase)
      (Term.weaken newType witness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next baseRecurse =>
            exfalso
            have totHyp := baseIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType baseCase))) = true :=
              baseRecurse ▸ totHyp
            cases this
        · split
          · next witnessRecurse =>
              exfalso
              have totHyp := witnessIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType witness))) = true :=
                witnessRecurse ▸ totHyp
              cases this
          · rfl

/-! ## Wave D: cubical / HoTT non-binder totality. -/

/-- 0-IH parametric atomic totality: `Term.equivReflId`.  One Ty
sub-payload (carrier), no Term IH. -/
theorem isTotalOnWeaken_equivReflId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) :
    IsTotalOnWeaken (Term.equivReflId (context := context) carrier) := by
  intro newType
  show (strengthenTyped? (Term.equivReflId
      (context := context.cons newType) carrier.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.equivReflIdAtId`.  One Ty
+ one RawTerm sub-payload, no Term IH. -/
theorem isTotalOnWeaken_equivReflIdAtId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope) (carrierRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.equivReflIdAtId (context := context)
      innerLevel innerLevelLt carrier carrierRaw) := by
  intro newType
  show (strengthenTyped? (Term.equivReflIdAtId
      (context := context.cons newType) innerLevel innerLevelLt
      carrier.weaken carrierRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next carrierRawFails =>
        exfalso
        have carrierRawSuccess :
            carrierRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierRaw :=
          RawTerm.strengthen?_weaken carrierRaw
        rw [carrierRawSuccess] at carrierRawFails
        cases carrierRawFails
    · rfl

/-- 1-IH non-binder totality: `Term.glueElim`.  One Ty (baseType) +
one RawTerm (boundaryWitness) + one Term IH (gluedValue). -/
theorem isTotalOnWeaken_glueElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIH : IsTotalOnWeaken gluedValue) :
    IsTotalOnWeaken (Term.glueElim modeIsUnivalent gluedValue) := by
  intro newType
  show (strengthenTyped? (Term.glueElim modeIsUnivalent
      (Term.weaken newType gluedValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next boundaryFails =>
        exfalso
        have boundarySuccess :
            boundaryWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some boundaryWitness :=
          RawTerm.strengthen?_weaken boundaryWitness
        rw [boundarySuccess] at boundaryFails
        cases boundaryFails
    · split
      · next gluedRecurse =>
          exfalso
          have totHyp := gluedIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType gluedValue))) = true :=
            gluedRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.hcomp`.  No Ty payloads in the
dispatcher arm — purely 2-IH. -/
theorem isTotalOnWeaken_hcomp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    {sidesValue : Term context carrierType sidesRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIH : IsTotalOnWeaken sidesValue)
    (capIH : IsTotalOnWeaken capValue) :
    IsTotalOnWeaken (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  intro newType
  show (strengthenTyped? (Term.hcomp modeIsUnivalent
      (Term.weaken newType sidesValue)
      (Term.weaken newType capValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next sidesRecurse =>
      exfalso
      have totHyp := sidesIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType sidesValue))) = true :=
        sidesRecurse ▸ totHyp
      cases this
  · split
    · next capRecurse =>
        exfalso
        have totHyp := capIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType capValue))) = true :=
          capRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.glueIntro`.  One Ty (baseType) +
one RawTerm (boundaryWitness) + two Term IH (baseValue, partialValue). -/
theorem isTotalOnWeaken_glueIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIH : IsTotalOnWeaken baseValue)
    (partialIH : IsTotalOnWeaken partialValue) :
    IsTotalOnWeaken (Term.glueIntro modeIsUnivalent baseType
      boundaryWitness baseValue partialValue) := by
  intro newType
  show (strengthenTyped? (Term.glueIntro modeIsUnivalent
      baseType.weaken boundaryWitness.weaken
      (Term.weaken newType baseValue)
      (Term.weaken newType partialValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next boundaryFails =>
        exfalso
        have boundarySuccess :
            boundaryWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some boundaryWitness :=
          RawTerm.strengthen?_weaken boundaryWitness
        rw [boundarySuccess] at boundaryFails
        cases boundaryFails
    · split
      · next baseRecurse =>
          exfalso
          have totHyp := baseIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType baseValue))) = true :=
            baseRecurse ▸ totHyp
          cases this
      · split
        · next partialRecurse =>
            exfalso
            have totHyp := partialIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType partialValue))) = true :=
              partialRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.transp`.  Two Ty (sourceType,
targetType) + two RawTerm (sourceTypeRaw, targetTypeRaw) + two Term
IH (typePath, sourceValue). -/
theorem isTotalOnWeaken_transp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    {typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (pathIH : IsTotalOnWeaken typePath)
    (sourceIH : IsTotalOnWeaken sourceValue) :
    IsTotalOnWeaken (Term.transp modeIsUnivalent universeLevel
      universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
      typePath sourceValue) := by
  intro newType
  show (strengthenTyped? (Term.transp modeIsUnivalent universeLevel
      universeLevelLt sourceType.weaken targetType.weaken
      sourceTypeRaw.weaken targetTypeRaw.weaken
      (Term.weaken newType typePath)
      (Term.weaken newType sourceValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next sourceTypeFails =>
      exfalso
      have sourceTypeSuccess :
          sourceType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some sourceType :=
        Ty.strengthen?_weaken sourceType
      rw [sourceTypeSuccess] at sourceTypeFails
      cases sourceTypeFails
  · split
    · next targetTypeFails =>
        exfalso
        have targetTypeSuccess :
            targetType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some targetType :=
          Ty.strengthen?_weaken targetType
        rw [targetTypeSuccess] at targetTypeFails
        cases targetTypeFails
    · split
      · next sourceRawFails =>
          exfalso
          have sourceRawSuccess :
              sourceTypeRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some sourceTypeRaw :=
            RawTerm.strengthen?_weaken sourceTypeRaw
          rw [sourceRawSuccess] at sourceRawFails
          cases sourceRawFails
      · split
        · next targetRawFails =>
            exfalso
            have targetRawSuccess :
                targetTypeRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some targetTypeRaw :=
              RawTerm.strengthen?_weaken targetTypeRaw
            rw [targetRawSuccess] at targetRawFails
            cases targetRawFails
        · split
          · next pathRecurse =>
              exfalso
              have totHyp := pathIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType typePath))) = true :=
                pathRecurse ▸ totHyp
              cases this
          · split
            · next sourceRecurse =>
                exfalso
                have totHyp := sourceIH newType
                unfold strengthenTyped? at totHyp
                have : Option.isSome (none (α := StrengtheningResult
                    (ContextStrengthening.dropNewest context newType)
                    (Term.weaken newType sourceValue))) = true :=
                  sourceRecurse ▸ totHyp
                cases this
            · rfl

/-- 1-IH non-binder totality: `Term.uaToEquiv`.  Two Ty (leftTy,
rightTy) + two RawTerm (leftTyRaw, rightTyRaw) + one Term IH (proof). -/
theorem isTotalOnWeaken_uaToEquiv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    {proof : Term context
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                     leftTyRaw rightTyRaw)
              proofRaw}
    (proofIH : IsTotalOnWeaken proof) :
    IsTotalOnWeaken (Term.uaToEquiv innerLevel innerLevelLt leftTy
      rightTy leftTyRaw rightTyRaw proof) := by
  intro newType
  show (strengthenTyped? (Term.uaToEquiv innerLevel innerLevelLt
      leftTy.weaken rightTy.weaken
      leftTyRaw.weaken rightTyRaw.weaken
      (Term.weaken newType proof))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftTyFails =>
      exfalso
      have leftTySuccess :
          leftTy.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftTy :=
        Ty.strengthen?_weaken leftTy
      rw [leftTySuccess] at leftTyFails
      cases leftTyFails
  · split
    · next rightTyFails =>
        exfalso
        have rightTySuccess :
            rightTy.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightTy :=
          Ty.strengthen?_weaken rightTy
        rw [rightTySuccess] at rightTyFails
        cases rightTyFails
    · split
      · next leftRawFails =>
          exfalso
          have leftRawSuccess :
              leftTyRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some leftTyRaw :=
            RawTerm.strengthen?_weaken leftTyRaw
          rw [leftRawSuccess] at leftRawFails
          cases leftRawFails
      · split
        · next rightRawFails =>
            exfalso
            have rightRawSuccess :
                rightTyRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some rightTyRaw :=
              RawTerm.strengthen?_weaken rightTyRaw
            rw [rightRawSuccess] at rightRawFails
            cases rightRawFails
        · split
          · next proofRecurse =>
              exfalso
              have totHyp := proofIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType proof))) = true :=
                proofRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.pathApp`.  One Ty (carrierType)
+ two RawTerm (leftEndpoint, rightEndpoint) + two Term IH (pathTerm,
intervalTerm). -/
theorem isTotalOnWeaken_pathApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm : Term context
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term context Ty.interval intervalRaw}
    (pathIH : IsTotalOnWeaken pathTerm)
    (intervalIH : IsTotalOnWeaken intervalTerm) :
    IsTotalOnWeaken (Term.pathApp modeIsUnivalent pathTerm
      intervalTerm) := by
  intro newType
  show (strengthenTyped? (Term.pathApp modeIsUnivalent
      (Term.weaken newType pathTerm)
      (Term.weaken newType intervalTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrierType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierType :=
        Ty.strengthen?_weaken carrierType
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next pathRecurse =>
            exfalso
            have totHyp := pathIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType pathTerm))) = true :=
              pathRecurse ▸ totHyp
            cases this
        · split
          · next intervalRecurse =>
              exfalso
              have totHyp := intervalIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType intervalTerm))) = true :=
                intervalRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.hcompPath`.  One Ty (carrierType)
+ two RawTerm (leftEndpoint, rightEndpoint) + two Term IH (sidesPath,
capValue). -/
theorem isTotalOnWeaken_hcompPath {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    (leftEndpoint rightEndpoint : RawTerm scope)
    {sidesPathRaw capRaw : RawTerm scope}
    {sidesPath :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIH : IsTotalOnWeaken sidesPath)
    (capIH : IsTotalOnWeaken capValue) :
    IsTotalOnWeaken (Term.hcompPath modeIsUnivalent leftEndpoint
      rightEndpoint sidesPath capValue) := by
  intro newType
  show (strengthenTyped? (Term.hcompPath modeIsUnivalent
      leftEndpoint.weaken rightEndpoint.weaken
      (Term.weaken newType sidesPath)
      (Term.weaken newType capValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrierType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierType :=
        Ty.strengthen?_weaken carrierType
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next sidesRecurse =>
            exfalso
            have totHyp := sidesIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType sidesPath))) = true :=
              sidesRecurse ▸ totHyp
            cases this
        · split
          · next capRecurse =>
              exfalso
              have totHyp := capIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType capValue))) = true :=
                capRecurse ▸ totHyp
              cases this
          · rfl

/-- 1-IH non-binder totality: `Term.uaIntroHet`.  Two implicit Ty
(carrierA, carrierB) + two RawTerm (carrierARaw, carrierBRaw) +
one Term IH (equivWitness).  Dispatcher chains 6 successes (2 Ty
implicit + 4 RawTerm) before the IH split. -/
theorem isTotalOnWeaken_uaIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    {equivWitness : Term context (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivIH : IsTotalOnWeaken equivWitness) :
    IsTotalOnWeaken (Term.uaIntroHet innerLevel innerLevelLt
      carrierARaw carrierBRaw equivWitness) := by
  intro newType
  show (strengthenTyped? (Term.uaIntroHet innerLevel innerLevelLt
      carrierARaw.weaken carrierBRaw.weaken
      (Term.weaken newType equivWitness))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next carrierARawFails =>
          exfalso
          have carrierARawSuccess :
              carrierARaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some carrierARaw :=
            RawTerm.strengthen?_weaken carrierARaw
          rw [carrierARawSuccess] at carrierARawFails
          cases carrierARawFails
      · split
        · next carrierBRawFails =>
            exfalso
            have carrierBRawSuccess :
                carrierBRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some carrierBRaw :=
              RawTerm.strengthen?_weaken carrierBRaw
            rw [carrierBRawSuccess] at carrierBRawFails
            cases carrierBRawFails
        · split
          · next forwardRawFails =>
              exfalso
              have forwardRawSuccess :
                  forwardRaw.weaken.partialStrengthen?
                      (ContextStrengthening.dropNewest context newType).back =
                    some forwardRaw :=
                RawTerm.strengthen?_weaken forwardRaw
              rw [forwardRawSuccess] at forwardRawFails
              cases forwardRawFails
          · split
            · next backwardRawFails =>
                exfalso
                have backwardRawSuccess :
                    backwardRaw.weaken.partialStrengthen?
                        (ContextStrengthening.dropNewest context newType).back =
                      some backwardRaw :=
                  RawTerm.strengthen?_weaken backwardRaw
                rw [backwardRawSuccess] at backwardRawFails
                cases backwardRawFails
            · split
              · next equivRecurse =>
                  exfalso
                  have totHyp := equivIH newType
                  unfold strengthenTyped? at totHyp
                  have : Option.isSome (none (α := StrengtheningResult
                      (ContextStrengthening.dropNewest context newType)
                      (Term.weaken newType equivWitness))) = true :=
                    equivRecurse ▸ totHyp
                  cases this
              · rfl

/-- 3-IH non-binder totality: `Term.natElim`.  Pure 3-IH (no Ty
payload in dispatcher arm). -/
theorem isTotalOnWeaken_natElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (zeroIH : IsTotalOnWeaken zeroBranch)
    (succIH : IsTotalOnWeaken succBranch) :
    IsTotalOnWeaken (Term.natElim scrutinee zeroBranch succBranch) := by
  intro newType
  show (strengthenTyped? (Term.natElim
      (Term.weaken newType scrutinee)
      (Term.weaken newType zeroBranch)
      (Term.weaken newType succBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next scrutineeRecurse =>
      exfalso
      have totHyp := scrutineeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType scrutinee))) = true :=
        scrutineeRecurse ▸ totHyp
      cases this
  · split
    · next zeroRecurse =>
        exfalso
        have totHyp := zeroIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType zeroBranch))) = true :=
          zeroRecurse ▸ totHyp
        cases this
    · split
      · next succRecurse =>
          exfalso
          have totHyp := succIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType succBranch))) = true :=
            succRecurse ▸ totHyp
          cases this
      · rfl

/-- 3-IH non-binder totality: `Term.natRec`.  Pure 3-IH (no Ty
payload in dispatcher arm). -/
theorem isTotalOnWeaken_natRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context
      (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (zeroIH : IsTotalOnWeaken zeroBranch)
    (succIH : IsTotalOnWeaken succBranch) :
    IsTotalOnWeaken (Term.natRec scrutinee zeroBranch succBranch) := by
  intro newType
  show (strengthenTyped? (Term.natRec
      (Term.weaken newType scrutinee)
      (Term.weaken newType zeroBranch)
      (Term.weaken newType succBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next scrutineeRecurse =>
      exfalso
      have totHyp := scrutineeIH newType
      unfold strengthenTyped? at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType scrutinee))) = true :=
        scrutineeRecurse ▸ totHyp
      cases this
  · split
    · next zeroRecurse =>
        exfalso
        have totHyp := zeroIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType zeroBranch))) = true :=
          zeroRecurse ▸ totHyp
        cases this
    · split
      · next succRecurse =>
          exfalso
          have totHyp := succIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType succBranch))) = true :=
            succRecurse ▸ totHyp
          cases this
      · rfl

/-- 3-IH non-binder totality: `Term.listElim`.  One Ty (elementType)
+ 3 Term IH (scrutinee, nilBranch, consBranch). -/
theorem isTotalOnWeaken_listElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch : Term context
      (Ty.arrow elementType
        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (nilIH : IsTotalOnWeaken nilBranch)
    (consIH : IsTotalOnWeaken consBranch) :
    IsTotalOnWeaken (Term.listElim scrutinee nilBranch consBranch) := by
  intro newType
  show (strengthenTyped? (Term.listElim
      (Term.weaken newType scrutinee)
      (Term.weaken newType nilBranch)
      (Term.weaken newType consBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next nilRecurse =>
          exfalso
          have totHyp := nilIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType nilBranch))) = true :=
            nilRecurse ▸ totHyp
          cases this
      · split
        · next consRecurse =>
            exfalso
            have totHyp := consIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType consBranch))) = true :=
              consRecurse ▸ totHyp
            cases this
        · rfl

/-- 3-IH non-binder totality: `Term.optionMatch`.  One Ty (elementType)
+ 3 Term IH (scrutinee, noneBranch, someBranch). -/
theorem isTotalOnWeaken_optionMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (noneIH : IsTotalOnWeaken noneBranch)
    (someIH : IsTotalOnWeaken someBranch) :
    IsTotalOnWeaken (Term.optionMatch scrutinee noneBranch someBranch) := by
  intro newType
  show (strengthenTyped? (Term.optionMatch
      (Term.weaken newType scrutinee)
      (Term.weaken newType noneBranch)
      (Term.weaken newType someBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementType :=
        Ty.strengthen?_weaken elementType
      rw [elementSuccess] at elementFails
      cases elementFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next noneRecurse =>
          exfalso
          have totHyp := noneIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType noneBranch))) = true :=
            noneRecurse ▸ totHyp
          cases this
      · split
        · next someRecurse =>
            exfalso
            have totHyp := someIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType someBranch))) = true :=
              someRecurse ▸ totHyp
            cases this
        · rfl

/-- 3-IH non-binder totality: `Term.eitherMatch`.  Three Ty (leftType,
rightType, motiveType) + 3 Term IH. -/
theorem isTotalOnWeaken_eitherMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee : Term context (Ty.eitherType leftType rightType)
      scrutineeRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (leftIH : IsTotalOnWeaken leftBranch)
    (rightIH : IsTotalOnWeaken rightBranch) :
    IsTotalOnWeaken (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  intro newType
  show (strengthenTyped? (Term.eitherMatch
      (Term.weaken newType scrutinee)
      (Term.weaken newType leftBranch)
      (Term.weaken newType rightBranch))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftType :=
        Ty.strengthen?_weaken leftType
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightType :=
          Ty.strengthen?_weaken rightType
        rw [rightSuccess] at rightFails
        cases rightFails
    · split
      · next motiveFails =>
          exfalso
          have motiveSuccess :
              motiveType.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some motiveType :=
            Ty.strengthen?_weaken motiveType
          rw [motiveSuccess] at motiveFails
          cases motiveFails
      · split
        · next scrutineeRecurse =>
            exfalso
            have totHyp := scrutineeIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType scrutinee))) = true :=
              scrutineeRecurse ▸ totHyp
            cases this
        · split
          · next leftRecurse =>
              exfalso
              have totHyp := leftIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType leftBranch))) = true :=
                leftRecurse ▸ totHyp
              cases this
          · split
            · next rightRecurse =>
                exfalso
                have totHyp := rightIH newType
                unfold strengthenTyped? at totHyp
                have : Option.isSome (none (α := StrengtheningResult
                    (ContextStrengthening.dropNewest context newType)
                    (Term.weaken newType rightBranch))) = true :=
                  rightRecurse ▸ totHyp
                cases this
            · rfl

/-- 2-IH non-binder totality: `Term.effectPerform`.  One RawTerm
(effectTag) + signature with two Ty carriers + two Term IH. -/
theorem isTotalOnWeaken_effectPerform {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag : Term context
      (Ty.effect operationSignature.argumentCarrier effectTag)
      operationRaw}
    {arguments : Term context operationSignature.argumentCarrier
      argumentsRaw}
    (operationIH : IsTotalOnWeaken operationTag)
    (argumentsIH : IsTotalOnWeaken arguments) :
    IsTotalOnWeaken (Term.effectPerform effectTag effectRow
      operationSignature canPerformOperation operationTag arguments) := by
  intro newType
  show (strengthenTyped? (Term.effectPerform effectTag.weaken
      effectRow
      (operationSignature.map
        (fun carrierType : Ty level scope =>
          (carrierType : Ty level scope).rename RawRenaming.weaken))
      (Effects.CanPerform.map
        (fun carrierType : Ty level scope =>
          (carrierType : Ty level scope).rename RawRenaming.weaken)
        canPerformOperation)
      (Term.weaken newType operationTag)
      (Term.weaken newType arguments))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next effectTagFails =>
      exfalso
      have effectTagSuccess :
          effectTag.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some effectTag :=
        RawTerm.strengthen?_weaken effectTag
      rw [effectTagSuccess] at effectTagFails
      cases effectTagFails
  · split
    · next argumentCarrierFails =>
        exfalso
        have argumentCarrierSuccess :
            (Effects.OperationSignature.map
              (fun carrierType : Ty level scope =>
                (carrierType : Ty level scope).rename RawRenaming.weaken)
              operationSignature).argumentCarrier.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some operationSignature.argumentCarrier := by
          change operationSignature.argumentCarrier.weaken.partialStrengthen?
              _ = _
          exact Ty.strengthen?_weaken operationSignature.argumentCarrier
        rw [argumentCarrierSuccess] at argumentCarrierFails
        cases argumentCarrierFails
    · split
      · next resultCarrierFails =>
          exfalso
          have resultCarrierSuccess :
              (Effects.OperationSignature.map
                (fun carrierType : Ty level scope =>
                  (carrierType : Ty level scope).rename RawRenaming.weaken)
                operationSignature).resultCarrier.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some operationSignature.resultCarrier := by
            change operationSignature.resultCarrier.weaken.partialStrengthen?
                _ = _
            exact Ty.strengthen?_weaken operationSignature.resultCarrier
          rw [resultCarrierSuccess] at resultCarrierFails
          cases resultCarrierFails
      · split
        · next operationRecurse =>
            exfalso
            have totHyp := operationIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType operationTag))) = true :=
              operationRecurse ▸ totHyp
            cases this
        · split
          · next argumentsRecurse =>
              exfalso
              have totHyp := argumentsIH newType
              unfold strengthenTyped? at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType arguments))) = true :=
                argumentsRecurse ▸ totHyp
              cases this
          · rfl

/-- 0-IH parametric atomic totality: `Term.piTyCode` (universe-code
for `Ty.piTy`).  Domain at outer scope; codomain at scope+1 (under
binder).  Codomain strengthen uses `back.lift` and the lift-after-
lift composition lemma. -/
theorem isTotalOnWeaken_piTyCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.piTyCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.piTyCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken
      (codomainCodeRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainCodeRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainCodeRaw := by
          have := RawTerm.partialStrengthen?_rename_some codomainCodeRaw
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.sigmaTyCode` (universe-code
for `Ty.sigmaTy`).  Same shape as `piTyCode`. -/
theorem isTotalOnWeaken_sigmaTyCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.sigmaTyCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.sigmaTyCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken
      (codomainCodeRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainCodeRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainCodeRaw := by
          have := RawTerm.partialStrengthen?_rename_some codomainCodeRaw
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 1-IH non-binder totality: `Term.fst`.  One Ty (firstType) at outer
scope + one Ty (secondType) at scope+1 (lift) + one Term IH.  The
secondType strengthen uses `back.lift`. -/
theorem isTotalOnWeaken_fst {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH : IsTotalOnWeaken pairTerm) :
    IsTotalOnWeaken (Term.fst pairTerm) := by
  intro newType
  show (strengthenTyped? (Term.fst (Term.weaken newType pairTerm))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstType :=
        Ty.strengthen?_weaken firstType
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some secondType := by
          have := Ty.partialStrengthen?_rename_some secondType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [secondSuccess] at secondFails
        cases secondFails
    · split
      · next pairRecurse =>
          exfalso
          have totHyp := pairIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType pairTerm))) = true :=
            pairRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.refineIntro`.  Predicate (RawTerm)
at scope+1 uses `back.lift`; baseValue and predicateProof are Term
IHs at outer scope. -/
theorem isTotalOnWeaken_refineIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term context baseType valueRaw}
    {predicateProof : Term context Ty.unit proofRaw}
    (baseIH : IsTotalOnWeaken baseValue)
    (proofIH : IsTotalOnWeaken predicateProof) :
    IsTotalOnWeaken (Term.refineIntro predicate baseValue
      predicateProof) := by
  intro newType
  show (strengthenTyped? (Term.refineIntro
      (predicate.rename RawRenaming.weaken.lift)
      (Term.weaken newType baseValue)
      (Term.weaken newType predicateProof))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next predicateFails =>
      exfalso
      have predicateSuccess :
          (predicate.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some predicate := by
        have := RawTerm.partialStrengthen?_rename_some predicate
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [RawTerm.rename_identity] at this
        exact this
      rw [predicateSuccess] at predicateFails
      cases predicateFails
  · split
    · next baseRecurse =>
        exfalso
        have totHyp := baseIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType baseValue))) = true :=
          baseRecurse ▸ totHyp
        cases this
    · split
      · next proofRecurse =>
          exfalso
          have totHyp := proofIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType predicateProof))) = true :=
            proofRecurse ▸ totHyp
          cases this
      · rfl

/-- 1-IH non-binder totality: `Term.refineElim`.  One Ty (baseType) at
outer scope + one RawTerm (predicate) at scope+1 + one Term IH. -/
theorem isTotalOnWeaken_refineElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) refinedRaw}
    (refinedIH : IsTotalOnWeaken refinedValue) :
    IsTotalOnWeaken (Term.refineElim refinedValue) := by
  intro newType
  show (strengthenTyped? (Term.refineElim (Term.weaken newType
      refinedValue))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next predicateFails =>
        exfalso
        have predicateSuccess :
            (predicate.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some predicate := by
          have := RawTerm.partialStrengthen?_rename_some predicate
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [RawTerm.rename_identity] at this
          exact this
        rw [predicateSuccess] at predicateFails
        cases predicateFails
    · split
      · next refinedRecurse =>
          exfalso
          have totHyp := refinedIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType refinedValue))) = true :=
            refinedRecurse ▸ totHyp
          cases this
      · rfl

/-- 0-IH parametric atomic totality: `Term.funextReflAtId`.  Two Ty
(domainType, codomainType) at outer scope + one RawTerm (applyRaw)
at scope+1.  No Term IH. -/
theorem isTotalOnWeaken_funextReflAtId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextReflAtId (context := context)
      domainType codomainType applyRaw) := by
  intro newType
  show (strengthenTyped? (Term.funextReflAtId
      (context := context.cons newType)
      domainType.weaken codomainType.weaken
      (applyRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyFails =>
          exfalso
          have applySuccess :
              (applyRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyRaw := by
            have := RawTerm.partialStrengthen?_rename_some applyRaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applySuccess] at applyFails
          cases applyFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.funextIntroHet`.  Two Ty +
two RawTerm at scope+1.  No Term IH. -/
theorem isTotalOnWeaken_funextIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyARaw applyBRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextIntroHet (context := context)
      domainType codomainType applyARaw applyBRaw) := by
  intro newType
  show (strengthenTyped? (Term.funextIntroHet
      (context := context.cons newType)
      domainType.weaken codomainType.weaken
      (applyARaw.rename RawRenaming.weaken.lift)
      (applyBRaw.rename RawRenaming.weaken.lift))).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType :=
        Ty.strengthen?_weaken domainType
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType :=
          Ty.strengthen?_weaken codomainType
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyAFails =>
          exfalso
          have applyASuccess :
              (applyARaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyARaw := by
            have := RawTerm.partialStrengthen?_rename_some applyARaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applyASuccess] at applyAFails
          cases applyAFails
      · split
        · next applyBFails =>
            exfalso
            have applyBSuccess :
                (applyBRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back.lift =
                  some applyBRaw := by
              have := RawTerm.partialStrengthen?_rename_some applyBRaw
                RawRenaming.weaken.lift RawRenaming.identity
                (ContextStrengthening.dropNewest context newType).back.lift
                (fun position =>
                  PartialRawRenaming.lift_dropNewest_weaken_lift position)
              rw [RawTerm.rename_identity] at this
              exact this
            rw [applyBSuccess] at applyBFails
            cases applyBFails
        · rfl

/-- 0-IH parametric atomic totality: `Term.arrowCode` (universe-code
for `Ty.arrow`).  Two RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_arrowCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.arrowCode (context := context) outerLevel
      levelLe domainCodeRaw codomainCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.arrowCode
      (context := context.cons newType) outerLevel levelLe
      domainCodeRaw.weaken codomainCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          domainCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainCodeRaw :=
        RawTerm.strengthen?_weaken domainCodeRaw
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            codomainCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainCodeRaw :=
          RawTerm.strengthen?_weaken codomainCodeRaw
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.productCode` (universe-code
for `Ty.product`).  Two RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_productCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.productCode (context := context) outerLevel
      levelLe firstCodeRaw secondCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.productCode
      (context := context.cons newType) outerLevel levelLe
      firstCodeRaw.weaken secondCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstCodeRaw :=
        RawTerm.strengthen?_weaken firstCodeRaw
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            secondCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some secondCodeRaw :=
          RawTerm.strengthen?_weaken secondCodeRaw
        rw [secondSuccess] at secondFails
        cases secondFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.sumCode` (universe-code
for `Ty.sum`). -/
theorem isTotalOnWeaken_sumCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.sumCode (context := context) outerLevel
      levelLe leftCodeRaw rightCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.sumCode
      (context := context.cons newType) outerLevel levelLe
      leftCodeRaw.weaken rightCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftCodeRaw :=
        RawTerm.strengthen?_weaken leftCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightCodeRaw :=
          RawTerm.strengthen?_weaken rightCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.listCode` (universe-code
for `Ty.listType`).  One RawTerm sub-payload. -/
theorem isTotalOnWeaken_listCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.listCode (context := context) outerLevel
      levelLe elementCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.listCode
      (context := context.cons newType) outerLevel levelLe
      elementCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementCodeRaw :=
        RawTerm.strengthen?_weaken elementCodeRaw
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.optionCode` (universe-code
for `Ty.optionType`).  One RawTerm sub-payload. -/
theorem isTotalOnWeaken_optionCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.optionCode (context := context) outerLevel
      levelLe elementCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.optionCode
      (context := context.cons newType) outerLevel levelLe
      elementCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next elementFails =>
      exfalso
      have elementSuccess :
          elementCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some elementCodeRaw :=
        RawTerm.strengthen?_weaken elementCodeRaw
      rw [elementSuccess] at elementFails
      cases elementFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.eitherCode` (universe-code
for `Ty.eitherType`).  Two RawTerm sub-payloads. -/
theorem isTotalOnWeaken_eitherCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.eitherCode (context := context) outerLevel
      levelLe leftCodeRaw rightCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.eitherCode
      (context := context.cons newType) outerLevel levelLe
      leftCodeRaw.weaken rightCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftCodeRaw :=
        RawTerm.strengthen?_weaken leftCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightCodeRaw :=
          RawTerm.strengthen?_weaken rightCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-- 0-IH parametric atomic totality: `Term.idCode` (universe-code
for `Ty.id`).  Three RawTerm sub-payloads at the outer scope. -/
theorem isTotalOnWeaken_idCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.idCode (context := context) outerLevel
      levelLe typeCodeRaw leftRaw rightRaw) := by
  intro newType
  show (strengthenTyped? (Term.idCode
      (context := context.cons newType) outerLevel levelLe
      typeCodeRaw.weaken leftRaw.weaken rightRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next typeFails =>
      exfalso
      have typeSuccess :
          typeCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some typeCodeRaw :=
        RawTerm.strengthen?_weaken typeCodeRaw
      rw [typeSuccess] at typeFails
      cases typeFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftRaw :=
          RawTerm.strengthen?_weaken leftRaw
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightRaw :=
            RawTerm.strengthen?_weaken rightRaw
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.equivCode` (universe-code
for `Ty.equiv`).  Two RawTerm sub-payloads. -/
theorem isTotalOnWeaken_equivCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.equivCode (context := context) outerLevel
      levelLe leftTypeCodeRaw rightTypeCodeRaw) := by
  intro newType
  show (strengthenTyped? (Term.equivCode
      (context := context.cons newType) outerLevel levelLe
      leftTypeCodeRaw.weaken rightTypeCodeRaw.weaken)).isSome
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      exfalso
      have leftSuccess :
          leftTypeCodeRaw.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftTypeCodeRaw :=
        RawTerm.strengthen?_weaken leftTypeCodeRaw
      rw [leftSuccess] at leftFails
      cases leftFails
  · split
    · next rightFails =>
        exfalso
        have rightSuccess :
            rightTypeCodeRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightTypeCodeRaw :=
          RawTerm.strengthen?_weaken rightTypeCodeRaw
        rw [rightSuccess] at rightFails
        cases rightFails
    · rfl

/-! ## Wave I: Eq.mpr-blocked ctor totality.

Seven constructors have a type-equality cast in their `Term.rename` arm
(via `Ty.subst0_rename_commute.symm ▸ ...`), so `Term.weaken nt (Term.<ctor> ...)`
produces an Eq.mpr-wrapped term.  This wrapping blocks the standard
`unfold + split` template because the dispatcher's pattern-match cannot
see the constructor head through the cast.

Resolution: ship per-ctor `weaken_<ctor>_eq` rewrite lemmas that expose
the structural shape (each is `rfl`), then use `strengthenTyped?_isSome_castInvariant`
to discharge the cast and reduce to the un-cast form, which the
standard template handles.

Three ctors have OUTER casts (appPi, snd, funextRefl) — the cast wraps
the whole Term.snd/Term.appPi/Term.funextRefl head.
One ctor (boolElim) has OUTER + INNER casts.
Three ctors (pair, equivIntroHet, oeqFunext) have INNER casts on
specific subterms (secondValue / leftInv+rightInv / pointwiseProof). -/

/-- `Term.weaken` arm reshape for `Term.snd`.

The rename arm of `Term.snd` wraps the constructed `Term.snd (rename pairTerm)`
in `(Ty.subst0_rename_commute ...).symm ▸ ...` to align the result type
with the expected post-rename shape.  This lemma exposes that wrapping
explicitly for use in totality proofs.

Proved by `rfl` because `Term.weaken := Term.rename ...` is `@[reducible]`
and the rename arm's body normalises to the cast-wrapped form. -/
theorem weaken_snd_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (newType : Ty level scope)
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    Term.weaken newType (Term.snd pairTerm) =
      ((Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd) :
       Term (context.cons newType)
         ((secondType.subst0 firstType pairRaw.fst).rename RawRenaming.weaken)
         (pairRaw.rename RawRenaming.weaken).snd) := by
  rfl

/-- 1-IH non-binder totality through Eq.mpr cast: `Term.snd`.

The Eq.mpr-blocked variant uses `weaken_snd_unfolds` + cast-invariance to
reduce to the standard `Term.snd` arm of the dispatcher.  Body shape
mirrors `isTotalOnWeaken_fst` after the cast discharge. -/
theorem isTotalOnWeaken_snd {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIH : IsTotalOnWeaken pairTerm) :
    IsTotalOnWeaken (Term.snd pairTerm) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd)).isSome by
    rw [weaken_snd_unfolds newType pairTerm]
    show ((Ty.subst0_rename_commute secondType firstType
        (RawTerm.fst pairRaw) RawRenaming.weaken).symm ▸
        (Term.snd (Term.weaken newType pairTerm) :
          Term (context.cons newType)
            ((secondType.rename RawRenaming.weaken.lift).subst0
              (firstType.rename RawRenaming.weaken)
              (pairRaw.fst.rename RawRenaming.weaken))
            (pairRaw.rename RawRenaming.weaken).snd)).strengthenTyped?.isSome = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      exfalso
      have firstSuccess :
          firstType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some firstType :=
        Ty.strengthen?_weaken firstType
      rw [firstSuccess] at firstFails
      cases firstFails
  · split
    · next secondFails =>
        exfalso
        have secondSuccess :
            (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some secondType := by
          have := Ty.partialStrengthen?_rename_some secondType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [secondSuccess] at secondFails
        cases secondFails
    · split
      · next pairRecurse =>
          exfalso
          have totHyp := pairIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType pairTerm))) = true :=
            pairRecurse ▸ totHyp
          cases this
      · rfl

/-- `Term.weaken` arm reshape for `Term.funextRefl`.

The rename arm wraps in `(funextReflType_rename ...).symm ▸ ...` to
align the result Ty index.  Proved by `rfl`. -/
theorem weaken_funextRefl_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    Term.weaken newType
        (Term.funextRefl (context := context) domainType codomainType applyRaw) =
      ((funextReflType_rename RawRenaming.weaken domainType codomainType applyRaw).symm ▸
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift)))) :
       Term (context.cons newType)
         ((funextReflType domainType codomainType applyRaw).rename RawRenaming.weaken)
         (RawTerm.lam (RawTerm.refl applyRaw)).weaken) := by
  rfl

/-- 0-IH parametric atomic totality through Eq.mpr cast: `Term.funextRefl`.

`Term.funextRefl` carries two Ty payloads + one RawTerm at scope+1
applyRaw.  No Term IH.  The rename arm has an outer Eq.mpr wrapping the
constructor; we discharge via cast invariance + the standard atomic
template (domain success, codomain success, apply success, rfl). -/
theorem isTotalOnWeaken_funextRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    IsTotalOnWeaken (Term.funextRefl (context := context)
      domainType codomainType applyRaw) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift))))).isSome by
    rw [weaken_funextRefl_unfolds newType domainType codomainType applyRaw]
    show ((funextReflType_rename RawRenaming.weaken
        domainType codomainType applyRaw).symm ▸
        (Term.funextRefl (context := context.cons newType)
          (domainType.rename RawRenaming.weaken)
          (codomainType.rename RawRenaming.weaken)
          (applyRaw.rename RawRenaming.weaken.lift) :
          Term (context.cons newType)
            (funextReflType (domainType.rename RawRenaming.weaken)
              (codomainType.rename RawRenaming.weaken)
              (applyRaw.rename RawRenaming.weaken.lift))
            (RawTerm.lam (RawTerm.refl
              (applyRaw.rename RawRenaming.weaken.lift))))).strengthenTyped?.isSome = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back
            (fun position => rfl)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next applyFails =>
          exfalso
          have applySuccess :
              (applyRaw.rename RawRenaming.weaken.lift).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back.lift =
                some applyRaw := by
            have := RawTerm.partialStrengthen?_rename_some applyRaw
              RawRenaming.weaken.lift RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back.lift
              (fun position =>
                PartialRawRenaming.lift_dropNewest_weaken_lift position)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [applySuccess] at applyFails
          cases applyFails
      · rfl

/-- `Term.weaken` arm reshape for `Term.appPi`.

The rename arm wraps in `(Ty.subst0_rename_commute ...).symm ▸ ...` to
align the result Ty index.  Proved by `rfl`. -/
theorem weaken_appPi_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (newType : Ty level scope)
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Term.weaken newType (Term.appPi functionTerm argumentTerm) =
      ((Ty.subst0_rename_commute codomainType domainType argumentRaw
          RawRenaming.weaken).symm ▸
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))) :
       Term (context.cons newType)
         ((codomainType.subst0 domainType argumentRaw).rename RawRenaming.weaken)
         (RawTerm.app functionRaw argumentRaw).weaken) := by
  rfl

/-- 2-IH non-binder totality through Eq.mpr cast: `Term.appPi`.

Dependent Π application — codomain at scope+1, two Term IH plus
domain/codomain Ty payloads.  Cast on the outer result; discharge via
weaken_appPi_unfolds + castInvariant. -/
theorem isTotalOnWeaken_appPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIH : IsTotalOnWeaken functionTerm)
    (argumentIH : IsTotalOnWeaken argumentTerm) :
    IsTotalOnWeaken (Term.appPi functionTerm argumentTerm) := by
  intro newType
  suffices uncastTotality :
      (strengthenTyped?
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken)))).isSome by
    rw [weaken_appPi_unfolds newType functionTerm argumentTerm]
    show ((Ty.subst0_rename_commute codomainType domainType argumentRaw
        RawRenaming.weaken).symm ▸
        (Term.appPi (Term.weaken newType functionTerm)
          (Term.weaken newType argumentTerm) :
          Term (context.cons newType)
            ((codomainType.rename RawRenaming.weaken.lift).subst0
              (domainType.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken))
            (RawTerm.app (functionRaw.rename RawRenaming.weaken)
              (argumentRaw.rename RawRenaming.weaken)))).strengthenTyped?.isSome
          = true
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken.lift).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back.lift =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken.lift RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back.lift
            (fun position =>
              PartialRawRenaming.lift_dropNewest_weaken_lift position)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next functionRecurse =>
          exfalso
          have totHyp := functionIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType functionTerm))) = true :=
            functionRecurse ▸ totHyp
          cases this
      · split
        · next argumentRecurse =>
            exfalso
            have totHyp := argumentIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType argumentTerm))) = true :=
              argumentRecurse ▸ totHyp
            cases this
        · rfl

/-- `Term.weaken` arm reshape for `Term.pair`.

The rename arm has INNER cast on `secondValue`: the head is `Term.pair`
(no outer cast), but the secondValue argument is wrapped in
`Ty.subst0_rename_commute ... ▸ ...`.  Proved by `rfl`.

Note: `Ty.weaken` is defined as `Ty.rename RawRenaming.weaken`, but
they may not be defeq in all positions; this lemma uses the
`.rename RawRenaming.weaken` form explicitly. -/
theorem weaken_pair_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (newType : Ty level scope)
    (firstValue : Term context firstType firstRaw)
    (secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    Term.weaken newType (Term.pair firstValue secondValue) =
      Term.pair (Term.weaken newType firstValue)
        ((Ty.subst0_rename_commute secondType firstType firstRaw
          RawRenaming.weaken) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) secondValue :
            Term (context.cons newType)
              ((secondType.subst0 firstType firstRaw).rename RawRenaming.weaken)
              (secondRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 2-IH non-binder totality through INNER Eq.mpr cast: `Term.pair`.

The cast is on the `secondValue` subterm, so the dispatcher's match on
`Term.pair` head succeeds, but the recursion on the cast term doesn't
directly hit the secondIH.  Use cast invariance to bridge the inner
cast back to the un-cast form. -/
theorem isTotalOnWeaken_pair {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIH : IsTotalOnWeaken firstValue)
    (secondIH : IsTotalOnWeaken secondValue) :
    IsTotalOnWeaken (Term.pair firstValue secondValue) := by
  intro newType
  -- Term.weaken nt (Term.pair fv sv) =
  --   Term.pair (Term.weaken nt fv) (eq ▸ Term.weaken nt sv)
  -- Rewrite via weaken_pair_unfolds to expose the inner cast explicitly,
  -- then the dispatcher's match on Term.pair head fires.
  rw [weaken_pair_unfolds newType firstValue secondValue]
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next secondTypeFails =>
      exfalso
      have secondTypeSuccess :
          (secondType.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some secondType := by
        have := Ty.partialStrengthen?_rename_some secondType
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [Ty.rename_identity] at this
        exact this
      rw [secondTypeSuccess] at secondTypeFails
      cases secondTypeFails
  · split
    · next firstRecurse =>
        exfalso
        have totHyp := firstIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType firstValue))) = true :=
          firstRecurse ▸ totHyp
        cases this
    · split
      · next secondRecurse =>
          exfalso
          -- secondRecurse : (eq ▸ Term.rename _ secondValue).partialStrengthenTyped? = none
          -- (Term.weaken newType secondValue = Term.rename (weakenStep) secondValue,
          --  definitional equality through @[reducible] Term.weaken.)
          --
          -- secondIH gives (Term.weaken nt sv).strengthenTyped?.isSome = true,
          -- castInvariant says (eq ▸ ...).strengthenTyped?.isSome = (...).strengthenTyped?.isSome,
          -- so secondRecurse's none contradicts.
          have totHyp := secondIH newType
          unfold strengthenTyped? at totHyp
          have invariance :=
            strengthenTyped?_isSome_castInvariant
              (Term.rename (TermRenaming.weakenStep context newType) secondValue)
              (Ty.subst0_rename_commute secondType firstType firstRaw
                RawRenaming.weaken)
          unfold strengthenTyped? at invariance
          -- invariance: (eq ▸ Term.rename ... sv).partialStrengthenTyped? _ .isSome
          --           = (Term.rename ... sv).partialStrengthenTyped? _ .isSome
          rw [secondRecurse] at invariance
          -- invariance: false = (Term.rename ... sv).partialStrengthenTyped? _ .isSome
          -- which is `Option.isSome none = ...`, i.e. `false = ...`
          -- After rw, invariance becomes `none.isSome = ...isSome`
          -- And totHyp says `... .isSome = true`
          rw [totHyp] at invariance
          cases invariance
      · rfl

/-- `Term.weaken` arm reshape for `Term.oeqFunext`.

Inner cast on `pointwiseProof` via `oeqFunextPointwiseType_rename`. -/
theorem weaken_oeqFunext_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    (pointwiseProof : Term context
      (oeqFunextPointwiseType domainType codomainType
        leftFunctionRaw rightFunctionRaw)
      pointwiseRaw) :
    Term.weaken newType
        (Term.oeqFunext (context := context) domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof) =
      Term.oeqFunext (context := context.cons newType)
        (domainType.rename RawRenaming.weaken)
        (codomainType.rename RawRenaming.weaken)
        (leftFunctionRaw.rename RawRenaming.weaken)
        (rightFunctionRaw.rename RawRenaming.weaken)
        ((oeqFunextPointwiseType_rename RawRenaming.weaken
          domainType codomainType leftFunctionRaw rightFunctionRaw) ▸
          (Term.rename (TermRenaming.weakenStep context newType) pointwiseProof :
            Term (context.cons newType)
              ((oeqFunextPointwiseType domainType codomainType
                leftFunctionRaw rightFunctionRaw).rename RawRenaming.weaken)
              (pointwiseRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 1-IH non-binder totality through INNER Eq.mpr cast: `Term.oeqFunext`. -/
theorem isTotalOnWeaken_oeqFunext {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    {pointwiseProof : Term context
      (oeqFunextPointwiseType domainType codomainType
        leftFunctionRaw rightFunctionRaw)
      pointwiseRaw}
    (pointwiseIH : IsTotalOnWeaken pointwiseProof) :
    IsTotalOnWeaken (Term.oeqFunext (context := context)
      domainType codomainType leftFunctionRaw rightFunctionRaw
      pointwiseProof) := by
  intro newType
  rw [weaken_oeqFunext_unfolds newType domainType codomainType
    leftFunctionRaw rightFunctionRaw pointwiseProof]
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      exfalso
      have domainSuccess :
          (domainType.rename RawRenaming.weaken).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some domainType := by
        have := Ty.partialStrengthen?_rename_some domainType
          RawRenaming.weaken RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back
          (fun position => rfl)
        rw [Ty.rename_identity] at this
        exact this
      rw [domainSuccess] at domainFails
      cases domainFails
  · split
    · next codomainFails =>
        exfalso
        have codomainSuccess :
            (codomainType.rename RawRenaming.weaken).partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some codomainType := by
          have := Ty.partialStrengthen?_rename_some codomainType
            RawRenaming.weaken RawRenaming.identity
            (ContextStrengthening.dropNewest context newType).back
            (fun position => rfl)
          rw [Ty.rename_identity] at this
          exact this
        rw [codomainSuccess] at codomainFails
        cases codomainFails
    · split
      · next leftFails =>
          exfalso
          have leftSuccess :
              (leftFunctionRaw.rename RawRenaming.weaken).partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some leftFunctionRaw := by
            have := RawTerm.partialStrengthen?_rename_some leftFunctionRaw
              RawRenaming.weaken RawRenaming.identity
              (ContextStrengthening.dropNewest context newType).back
              (fun position => rfl)
            rw [RawTerm.rename_identity] at this
            exact this
          rw [leftSuccess] at leftFails
          cases leftFails
      · split
        · next rightFails =>
            exfalso
            have rightSuccess :
                (rightFunctionRaw.rename RawRenaming.weaken).partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some rightFunctionRaw := by
              have := RawTerm.partialStrengthen?_rename_some rightFunctionRaw
                RawRenaming.weaken RawRenaming.identity
                (ContextStrengthening.dropNewest context newType).back
                (fun position => rfl)
              rw [RawTerm.rename_identity] at this
              exact this
            rw [rightSuccess] at rightFails
            cases rightFails
        · split
          · next pointwiseRecurse =>
              exfalso
              -- INNER CAST: pointwiseRecurse : (eq ▸ Term.rename _ pp).partialStrengthenTyped? = none
              have totHyp := pointwiseIH newType
              unfold strengthenTyped? at totHyp
              have invariance :=
                strengthenTyped?_isSome_castInvariant
                  (Term.rename
                    (TermRenaming.weakenStep context newType) pointwiseProof)
                  (oeqFunextPointwiseType_rename RawRenaming.weaken
                    domainType codomainType leftFunctionRaw rightFunctionRaw)
              unfold strengthenTyped? at invariance
              rw [pointwiseRecurse] at invariance
              rw [totHyp] at invariance
              cases invariance
          · rfl

/-- `Term.weaken` arm reshape for `Term.equivIntroHet`.

Two inner casts on `leftInv` and `rightInv`. -/
theorem weaken_equivIntroHet_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    (newType : Ty level scope)
    (forward : Term context (Ty.arrow carrierA carrierB) forwardRaw)
    (backward : Term context (Ty.arrow carrierB carrierA) backwardRaw)
    (leftInv : Term context
      (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
      leftInvRaw)
    (rightInv : Term context
      (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
      rightInvRaw) :
    Term.weaken newType
        (Term.equivIntroHet forward backward leftInv rightInv) =
      Term.equivIntroHet
        (Term.weaken newType forward)
        (Term.weaken newType backward)
        ((equivIntroHetLeftInverseType_rename RawRenaming.weaken
          carrierA forwardRaw backwardRaw) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) leftInv :
            Term (context.cons newType)
              ((equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw).rename
                RawRenaming.weaken)
              (leftInvRaw.rename RawRenaming.weaken)))
        ((equivIntroHetRightInverseType_rename RawRenaming.weaken
          carrierB forwardRaw backwardRaw) ▸
          (Term.rename
            (TermRenaming.weakenStep context newType) rightInv :
            Term (context.cons newType)
              ((equivIntroHetRightInverseType carrierB forwardRaw backwardRaw).rename
                RawRenaming.weaken)
              (rightInvRaw.rename RawRenaming.weaken))) := by
  rfl

/-- 4-IH non-binder totality through TWO INNER Eq.mpr casts: `Term.equivIntroHet`. -/
theorem isTotalOnWeaken_equivIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward : Term context (Ty.arrow carrierA carrierB) forwardRaw}
    {backward : Term context (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv : Term context
      (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
      leftInvRaw}
    {rightInv : Term context
      (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
      rightInvRaw}
    (forwardIH : IsTotalOnWeaken forward)
    (backwardIH : IsTotalOnWeaken backward)
    (leftInvIH : IsTotalOnWeaken leftInv)
    (rightInvIH : IsTotalOnWeaken rightInv) :
    IsTotalOnWeaken (Term.equivIntroHet forward backward leftInv rightInv) := by
  intro newType
  rw [weaken_equivIntroHet_unfolds newType forward backward leftInv rightInv]
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next forwardRecurse =>
          exfalso
          have totHyp := forwardIH newType
          unfold strengthenTyped? at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType forward))) = true :=
            forwardRecurse ▸ totHyp
          cases this
      · split
        · next backwardRecurse =>
            exfalso
            have totHyp := backwardIH newType
            unfold strengthenTyped? at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType backward))) = true :=
              backwardRecurse ▸ totHyp
            cases this
        · split
          · next leftInvRecurse =>
              exfalso
              -- INNER CAST on leftInv
              have totHyp := leftInvIH newType
              unfold strengthenTyped? at totHyp
              have invariance :=
                strengthenTyped?_isSome_castInvariant
                  (Term.rename (TermRenaming.weakenStep context newType) leftInv)
                  (equivIntroHetLeftInverseType_rename RawRenaming.weaken
                    carrierA forwardRaw backwardRaw)
              unfold strengthenTyped? at invariance
              rw [leftInvRecurse] at invariance
              rw [totHyp] at invariance
              cases invariance
          · split
            · next rightInvRecurse =>
                exfalso
                -- INNER CAST on rightInv
                have totHyp := rightInvIH newType
                unfold strengthenTyped? at totHyp
                have invariance :=
                  strengthenTyped?_isSome_castInvariant
                    (Term.rename (TermRenaming.weakenStep context newType) rightInv)
                    (equivIntroHetRightInverseType_rename RawRenaming.weaken
                      carrierB forwardRaw backwardRaw)
                unfold strengthenTyped? at invariance
                rw [rightInvRecurse] at invariance
                rw [totHyp] at invariance
                cases invariance
            · rfl

/-- `Term.weaken` arm reshape for `Term.boolElim`.

Combined OUTER + 2 INNER casts (thenBranch, elseBranch).  Cumulative
Eq.mpr blocking; resolved by the same castInvariant strategy applied
at all three cast sites.  Proved by `rfl`. -/
theorem weaken_boolElim_unfolds {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (newType : Ty level scope)
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Term.weaken newType (Term.boolElim scrutinee thenBranch elseBranch) =
      ((Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw
          RawRenaming.weaken).symm ▸
        (Term.boolElim
          (motiveType := motiveType.rename RawRenaming.weaken.lift)
          (Term.weaken newType scrutinee)
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) thenBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolTrue).rename
                  RawRenaming.weaken)
                (thenRaw.rename RawRenaming.weaken)))
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) elseBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolFalse).rename
                  RawRenaming.weaken)
                (elseRaw.rename RawRenaming.weaken))) :
          Term (context.cons newType)
            ((motiveType.rename RawRenaming.weaken.lift).subst0 Ty.bool
              (scrutineeRaw.rename RawRenaming.weaken))
            (RawTerm.boolElim
              (scrutineeRaw.rename RawRenaming.weaken)
              (thenRaw.rename RawRenaming.weaken)
              (elseRaw.rename RawRenaming.weaken))) :
       Term (context.cons newType)
         ((motiveType.subst0 Ty.bool scrutineeRaw).rename RawRenaming.weaken)
         (RawTerm.boolElim scrutineeRaw thenRaw elseRaw).weaken) := by
  rfl

/-- 3-IH non-binder totality through OUTER + 2 INNER Eq.mpr casts: `Term.boolElim`. -/
theorem isTotalOnWeaken_boolElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term context Ty.bool scrutineeRaw}
    {thenBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch : Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH : IsTotalOnWeaken scrutinee)
    (thenIH : IsTotalOnWeaken thenBranch)
    (elseIH : IsTotalOnWeaken elseBranch) :
    IsTotalOnWeaken (Term.boolElim scrutinee thenBranch elseBranch) := by
  intro newType
  -- Discharge OUTER cast first via suffices + castInvariant
  suffices uncastTotality :
      (strengthenTyped?
        (Term.boolElim
          (motiveType := motiveType.rename RawRenaming.weaken.lift)
          (Term.weaken newType scrutinee)
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) thenBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolTrue).rename
                  RawRenaming.weaken)
                (thenRaw.rename RawRenaming.weaken)))
          ((Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
            RawRenaming.weaken) ▸
            (Term.rename
              (TermRenaming.weakenStep context newType) elseBranch :
              Term (context.cons newType)
                ((motiveType.subst0 Ty.bool RawTerm.boolFalse).rename
                  RawRenaming.weaken)
                (elseRaw.rename RawRenaming.weaken))) :
          Term (context.cons newType)
            ((motiveType.rename RawRenaming.weaken.lift).subst0 Ty.bool
              (scrutineeRaw.rename RawRenaming.weaken))
            (RawTerm.boolElim
              (scrutineeRaw.rename RawRenaming.weaken)
              (thenRaw.rename RawRenaming.weaken)
              (elseRaw.rename RawRenaming.weaken)))).isSome by
    rw [weaken_boolElim_unfolds newType scrutinee thenBranch elseBranch]
    rw [strengthenTyped?_isSome_castInvariant]
    exact uncastTotality
  unfold strengthenTyped?
  unfold partialStrengthenTyped?
  split
  · next motiveFails =>
      exfalso
      have motiveSuccess :
          (motiveType.rename RawRenaming.weaken.lift).partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back.lift =
            some motiveType := by
        have := Ty.partialStrengthen?_rename_some motiveType
          RawRenaming.weaken.lift RawRenaming.identity
          (ContextStrengthening.dropNewest context newType).back.lift
          (fun position =>
            PartialRawRenaming.lift_dropNewest_weaken_lift position)
        rw [Ty.rename_identity] at this
        exact this
      rw [motiveSuccess] at motiveFails
      cases motiveFails
  · split
    · next scrutineeRecurse =>
        exfalso
        have totHyp := scrutineeIH newType
        unfold strengthenTyped? at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType scrutinee))) = true :=
          scrutineeRecurse ▸ totHyp
        cases this
    · split
      · next thenRecurse =>
          exfalso
          -- INNER CAST on thenBranch
          have totHyp := thenIH newType
          unfold strengthenTyped? at totHyp
          change
            (partialStrengthenTyped?
              (Term.rename
                (TermRenaming.weakenStep context newType) thenBranch)
              (ContextStrengthening.dropNewest context newType)).isSome = true at totHyp
          have invariance :=
            strengthenTyped?_isSome_castInvariant
              (Term.rename
                (TermRenaming.weakenStep context newType) thenBranch)
              (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue
                RawRenaming.weaken)
          unfold strengthenTyped? at invariance
          -- invariance : isSome cast = isSome uncast
          -- totHyp : isSome uncast = true
          -- => isSome cast = true
          -- thenRecurse : cast = none
          -- => isSome cast = false (via congrArg)
          -- Combine: true = false
          have isSomeCastTrue : _ = _ := invariance.trans totHyp
          have isSomeCastFalse : _ = _ := congrArg Option.isSome thenRecurse
          have contradiction : (true : Bool) = false := isSomeCastTrue.symm.trans isSomeCastFalse
          cases contradiction
      · split
        · next elseRecurse =>
            exfalso
            have totHyp := elseIH newType
            unfold strengthenTyped? at totHyp
            change
              (partialStrengthenTyped?
                (Term.rename
                  (TermRenaming.weakenStep context newType) elseBranch)
                (ContextStrengthening.dropNewest context newType)).isSome = true at totHyp
            have invariance :=
              strengthenTyped?_isSome_castInvariant
                (Term.rename
                  (TermRenaming.weakenStep context newType) elseBranch)
                (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse
                  RawRenaming.weaken)
            unfold strengthenTyped? at invariance
            have isSomeCastTrue : _ = _ := invariance.trans totHyp
            have isSomeCastFalse : _ = _ := congrArg Option.isSome elseRecurse
            have contradiction : (true : Bool) = false := isSomeCastTrue.symm.trans isSomeCastFalse
            cases contradiction
        · rfl

/-- BIG-ASS THEOREM headline — closed-atomic unweaken? recovers source.

For each of the 7 closed-atomic ctors, `Term.unweaken?` applied to
`Term.weaken newType (Term.<ctor>)` returns `some (Term.<ctor>)`.
Direct `rfl`-witnesses because the dispatcher's success and the
type/raw alignment unfolds atomically. -/
theorem unweaken?_weaken_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.unit (context := context))) = some Term.unit := by
  rfl

theorem unweaken?_weaken_boolTrue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.boolTrue (context := context))) = some Term.boolTrue := by
  rfl

theorem unweaken?_weaken_boolFalse {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.boolFalse (context := context))) = some Term.boolFalse := by
  rfl

theorem unweaken?_weaken_natZero {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.natZero (context := context))) = some Term.natZero := by
  rfl

theorem unweaken?_weaken_interval0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.interval0 (context := context))) = some Term.interval0 := by
  rfl

theorem unweaken?_weaken_interval1 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.interval1 (context := context))) = some Term.interval1 := by
  rfl

theorem unweaken?_weaken_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) (position : Fin scope) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.var (context := context) position)) =
      some (Term.var position) := by
  rfl

/-- Phase 2.A: 0-IH parametric atomic — `universeCode` equation form. -/
theorem unweaken?_weaken_universeCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.unweaken? (Term.weaken (context := context) newType
        (Term.universeCode (context := context) innerLevel outerLevel
          cumulOk levelLe)) =
      some (Term.universeCode innerLevel outerLevel cumulOk levelLe) := by
  rfl


/-- Genuine iff (atomic-base version) — non-tautological strengthening
of `weaken_image_iff_strengthenTyped?_some`.

The original Step-3 iff is structural sugar around `Term.unweaken?`'s
definition (both witnesses succeed under identical conditions because
`unweaken?` pattern-matches on `strengthenTyped?`).  This version
adds genuine totality content: on a CLOSED ATOMIC SOURCE TERM (one of
the 7 atomics), the iff witnesses are UNCONDITIONALLY inhabited — no
side hypothesis required.

Consumers proving Step.eta-cascade subject reduction on closed atomic
source terms can invoke this directly. -/
theorem weaken_image_iff_strengthenTyped?_some_TRUE_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope) :
    (∃ originalTerm,
        Term.unweaken? (Term.weaken (context := context) newType
            (Term.unit (context := context))) = some originalTerm) ∧
      ∃ result,
        strengthenTyped? (Term.weaken (context := context) newType
            (Term.unit (context := context))) = some result :=
  ⟨⟨Term.unit, unweaken?_weaken_unit newType⟩,
   ⟨partialStrengthenTypedUnit
      (ContextStrengthening.dropNewest context newType), rfl⟩⟩

/-! ## Phase X bridge: IsAggregatorTotal (weakened term) → IsTotalOnWeaken.

`IsTotalOnWeaken sourceTerm` asserts that the dispatcher succeeds on
the WEAKENED form `Term.weaken newType sourceTerm` for any
`newType : Ty level scope`.  `IsAggregatorTotal weakenedTerm` is the
strictly stronger universal-strengthening statement on a
sourceTerm-bearing weakenedTerm.

This bridge specializes the universal statement to the canonical
`dropNewest` strengthening: when `IsAggregatorTotal (Term.weaken
newType sourceTerm)` holds for every choice of `newType`, the
`dropNewest context newType` strengthening witnesses
`IsTotalOnWeaken sourceTerm` because the source/raw indices of
`Term.weaken newType sourceTerm` are already weakened forms of
`sourceTerm`'s indices, and `Ty.strengthen?_weaken` /
`RawTerm.strengthen?_weaken` discharge the index witnesses.

This is the load-bearing path for the three binder wrappers
(`lam`, `lamPi`, `pathLam`) whose body strengthens through the
LIFTED `dropNewest`: the body's `IsAggregatorTotal` IH supplies the
universal-strengthening parameter, the binder's
`isAggregatorTotal_<binder>` derivation lifts that into
`IsAggregatorTotal (Term.<binder> ...)`, and this bridge converts
the conclusion into the consumer-facing `IsTotalOnWeaken`
predicate. -/
theorem isTotalOnWeaken_of_weaken_isAggregatorTotal
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (weakenTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal (Term.weaken newType sourceTerm)) :
    IsTotalOnWeaken sourceTerm := by
  intro newType
  exact weakenTotal newType
    (ContextStrengthening.dropNewest context newType)
    (Ty.strengthen?_weaken sourceType)
    (RawTerm.strengthen?_weaken sourceRaw)

/-! ## Phase X: the three binder wrappers.

The non-binder ctors (the 75 already-shipped `isTotalOnWeaken_<ctor>`
theorems) all take `IsTotalOnWeaken child` IHs on their recursive
children — the narrow predicate suffices because the dispatcher's
recursion on a non-binder child uses `dropNewest`, matching the
predicate's `Term.weaken newType` shape directly.

The three binder ctors (`lam`, `lamPi`, `pathLam`) break this
pattern: their body's strengthening goes through `strengthening.lift`,
not `dropNewest`.  The narrow `IsTotalOnWeaken body` predicate cannot
transport through the lift; the strictly stronger
`IsAggregatorTotal body` (universal over all strengthenings of body)
must take its place as the binder IH.

Each wrapper's hypothesis is `weakenedBinderTotal`:
`∀ newType, IsAggregatorTotal (Term.weaken newType (Term.<binder> ...))`.
Downstream, this is constructed by:
1. taking `bodyTotal : IsAggregatorTotal body`,
2. transporting it under the binder's required renaming
   (`(weakenStep _).lift _` for the body of a weakened binder) — the
   typed rename-compatibility transport, ~78-case structural
   recursion, lives in the `Term.rename` cascade,
3. lifting through `isAggregatorTotal_<binder>`,
4. and arriving at the wrapper's `weakenedBinderTotal` hypothesis.

The bridge `isTotalOnWeaken_of_weaken_isAggregatorTotal` then
specializes the universal statement to `dropNewest` at each
`newType`, recovering `IsTotalOnWeaken (Term.<binder> ...)`. -/

/-- Binder totality wrapper: `Term.lam`.

Takes the per-`newType` `IsAggregatorTotal` on the weakened lam term,
which encapsulates the rename-transport of body's
`IsAggregatorTotal` through the dispatcher's lifted strengthening.
Converts to the consumer-facing `IsTotalOnWeaken` via the canonical
`dropNewest` specialization (the Phase X bridge above). -/
theorem isTotalOnWeaken_lam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {body : Term (context.cons domainType) codomainType.weaken bodyRaw}
    (weakenedLamTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.lam (context := context) (domainType := domainType)
              (codomainType := codomainType) body))) :
    IsTotalOnWeaken
      (Term.lam (context := context) (domainType := domainType)
        (codomainType := codomainType) body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedLamTotal

/-- Binder totality wrapper: `Term.lamPi`.

Dependent-Pi lambda; body lives at the lifted codomain inside the
binder.  Same structural shape as `isTotalOnWeaken_lam` modulo the
codomain's scope — proof is one application of the Phase X bridge. -/
theorem isTotalOnWeaken_lamPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {body : Term (context.cons domainType) codomainType bodyRaw}
    (weakenedLamPiTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.lamPi (context := context) (domainType := domainType)
              (codomainType := codomainType) body))) :
    IsTotalOnWeaken
      (Term.lamPi (context := context) (domainType := domainType)
        (codomainType := codomainType) body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedLamPiTotal

/-- Binder totality wrapper: `Term.pathLam`.

Cubical path lambda; body binds an interval slot with carrier
weakened.  Same Phase X bridge specialization as the other two
binders. -/
theorem isTotalOnWeaken_pathLam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {body :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    (weakenedPathLamTotal :
      ∀ (newType : Ty level scope),
        IsAggregatorTotal
          (Term.weaken newType
            (Term.pathLam (context := context) modeIsUnivalent carrierType
              leftEndpoint rightEndpoint body))) :
    IsTotalOnWeaken
      (Term.pathLam (context := context) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body) :=
  isTotalOnWeaken_of_weaken_isAggregatorTotal weakenedPathLamTotal

end Term

end LeanFX2
