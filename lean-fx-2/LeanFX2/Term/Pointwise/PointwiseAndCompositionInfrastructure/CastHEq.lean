import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.Composition

/-! # LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq

Semantic slice of typed pointwise substitution and composition infrastructure. -/

namespace LeanFX2

/-! ## Beta-specific singleton composition

These lemmas package the substitution shape used by lambda beta
contracta.  They live at the Term layer because they mention only
`Ty`, `RawTerm`, and `TermSubst`, while downstream reducibility lemmas
consume them to relate body IHs under an extended substitution to the
concrete `Term.subst0` contractum. -/

/-- A type-index cast on a typed term is heterogeneously equal to the
original term. -/
theorem Term.type_eq_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {raw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term context sourceType raw) :
    HEq (typeEq ▸ sourceTerm) sourceTerm := by
  cases typeEq
  exact HEq.rfl

/-- A symmetric type-index cast on a typed term is heterogeneously
equal to the original term. -/
theorem Term.type_eq_symm_cast_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {raw : RawTerm scope}
    (typeEq : sourceType = targetType)
    {targetTerm : Term context targetType raw} :
    HEq (typeEq.symm ▸ targetTerm) targetTerm := by
  cases typeEq
  exact HEq.rfl

/-- The freshly-bound variable is stable under equality of the single
head type added to the context. -/
theorem Term.var_zero_cons_type_eq_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    (typeEq : firstType = secondType) :
    HEq
      (Term.var (context := context.cons firstType)
        ⟨0, Nat.zero_lt_succ scope⟩)
      (Term.var (context := context.cons secondType)
        ⟨0, Nat.zero_lt_succ scope⟩) := by
  cases typeEq
  exact HEq.rfl

/-- Renaming ignores a pure symmetric type-index cast up to the
corresponding renamed type-index cast. -/
theorem Term.rename_type_eq_symm_cast_heq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {sourceType targetType : Ty level sourceScope}
    {raw : RawTerm sourceScope}
    (typeEq : sourceType = targetType)
    {targetTerm : Term sourceCtx targetType raw} :
    HEq (Term.rename termRenaming (typeEq.symm ▸ targetTerm))
      ((congrArg (fun someType => Ty.rename someType rho) typeEq).symm ▸
        Term.rename termRenaming targetTerm) := by
  cases typeEq
  exact HEq.rfl

/-- Renaming ignores a pure forward type-index cast up to the
corresponding renamed type-index cast. -/
theorem Term.rename_type_eq_cast_heq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {sourceType targetType : Ty level sourceScope}
    {raw : RawTerm sourceScope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term sourceCtx sourceType raw) :
    HEq (Term.rename termRenaming (typeEq ▸ sourceTerm))
      ((congrArg (fun someType => Ty.rename someType rho) typeEq) ▸
        Term.rename termRenaming sourceTerm) := by
  cases typeEq
  exact HEq.rfl

/-- Renaming preserves heterogeneous equality once source indices are
aligned by explicit type/raw equalities. -/
theorem Term.rename_heq_of_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType secondType : Ty level sourceScope}
    {firstRaw secondRaw : RawTerm sourceScope}
    (typeEq : firstType = secondType)
    (rawEq : firstRaw = secondRaw)
    {firstTerm : Term sourceCtx firstType firstRaw}
    {secondTerm : Term sourceCtx secondType secondRaw}
    (termsHEq : HEq firstTerm secondTerm) :
    HEq (Term.rename termRenaming firstTerm)
      (Term.rename termRenaming secondTerm) := by
  subst typeEq
  subst rawEq
  have termsEq : firstTerm = secondTerm := eq_of_heq termsHEq
  subst termsEq
  rfl

/-- Weakening a term is stable under equality of the new head type. -/
theorem Term.weaken_head_type_eq_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType secondType : Ty level scope}
    (typeEq : firstType = secondType)
    {sourceType : Ty level scope}
    {raw : RawTerm scope}
    (sourceTerm : Term context sourceType raw) :
    HEq (Term.weaken firstType sourceTerm)
      (Term.weaken secondType sourceTerm) := by
  cases typeEq
  exact HEq.rfl

/-- Weakening preserves heterogeneous equality once source indices are
aligned by explicit type/raw equalities. -/
theorem Term.weaken_heq_of_eq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {firstType secondType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    (typeEq : firstType = secondType)
    (rawEq : firstRaw = secondRaw)
    {firstTerm : Term context firstType firstRaw}
    {secondTerm : Term context secondType secondRaw}
    (termsHEq : HEq firstTerm secondTerm) :
    HEq (Term.weaken newType firstTerm)
      (Term.weaken newType secondTerm) := by
  subst typeEq
  subst rawEq
  have termsEq : firstTerm = secondTerm := eq_of_heq termsHEq
  subst termsEq
  rfl

end LeanFX2
