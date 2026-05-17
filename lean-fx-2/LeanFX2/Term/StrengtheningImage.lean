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
binder structure), so the full aggregator lands in multiple phases.

This file ships the entry point: a single uniform soundness
property `IsAggregatorSound`, plus a base-case dispatcher for the
`var` arm.  Subsequent ctors land as further dispatchers extending
the same predicate. -/

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

This is the FIRST shipped dispatcher arm of the headline
aggregator; remaining 77 arms land in subsequent phases. -/
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

end Term

end LeanFX2
