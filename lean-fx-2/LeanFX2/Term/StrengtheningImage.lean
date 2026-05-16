import LeanFX2.Term.TypedInversion
import LeanFX2.Term.HEqCongr

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

end Term

end LeanFX2
