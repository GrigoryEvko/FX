import LeanFX2.Reducibility.TypedCR2Direct

/-! # LeanFX2.Reducibility.TypedCR2Generic.HEqCasts

HEq/cast helpers that transport reducibility across type-index
or raw-index equalities.  Covers `Term.rename_type_eq_*`,
`Reducible.of_type_eq_*`, `Reducible.of_raw_eq_*`, and
`Reducible.of_heq`.

## Root status

Layer 3 metatheory leaf.  Second slice of `TypedCR2Generic`. -/

namespace LeanFX2


/-- Renaming a term cast by a symmetric type equality is HEq to casting
the renamed term by the renamed type equality.

This isolates the common cast-commutation step needed when stability
proofs pass through `TermSubst` entries whose implementation stores
typed terms behind `Eq.rec` casts. -/
theorem Term.rename_type_eq_symm_cast_HEq
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
  rfl

/-- Renaming a term cast by a forward type equality is HEq to casting
the renamed term by the renamed type equality.

This is the forward-cast companion to
`Term.rename_type_eq_symm_cast_HEq`; `TermSubst.renameOutput` stores
entries behind forward `Ty.subst_rename_commute` casts, so stability of
post-composed substitutions needs this exact `Eq.rec` shape. -/
theorem Term.rename_type_eq_cast_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {sourceType targetType : Ty level sourceScope}
    {raw : RawTerm sourceScope}
    (typeEq : sourceType = targetType)
    {sourceTerm : Term sourceCtx sourceType raw} :
    HEq (Term.rename termRenaming (typeEq ▸ sourceTerm))
      ((congrArg (fun someType => Ty.rename someType rho) typeEq) ▸
        Term.rename termRenaming sourceTerm) := by
  cases typeEq
  rfl

/-- A term cast by a symmetric type equality is HEq to the original
term. -/
theorem Term.type_eq_symm_cast_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {raw : RawTerm scope}
    (typeEq : sourceType = targetType)
    {targetTerm : Term context targetType raw} :
    HEq (typeEq.symm ▸ targetTerm) targetTerm := by
  cases typeEq
  rfl

/-- Renaming a term cast by symmetric raw and type equalities is HEq to
casting the renamed term by the renamed equalities.

This is the two-index companion to `Term.rename_type_eq_symm_cast_HEq`
for `TermSubst.consSingleton`, whose successor entries are stored
behind both a raw-index cast and a type-index cast. -/
theorem Term.rename_raw_type_eq_symm_cast_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    (typeEq : sourceType = targetType)
    (rawEq : sourceRaw = targetRaw)
    {targetTerm : Term sourceCtx targetType targetRaw} :
    HEq
      (Term.rename termRenaming (rawEq.symm ▸ typeEq.symm ▸ targetTerm))
      ((congrArg (fun someRaw => RawTerm.rename someRaw rho) rawEq).symm ▸
        (congrArg (fun someType => Ty.rename someType rho) typeEq).symm ▸
          Term.rename termRenaming targetTerm) := by
  cases typeEq
  cases rawEq
  rfl

/-- A term cast by symmetric raw and type equalities is HEq to the
original term. -/
theorem Term.raw_type_eq_symm_cast_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (rawEq : sourceRaw = targetRaw)
    {targetTerm : Term context targetType targetRaw} :
    HEq (rawEq.symm ▸ typeEq.symm ▸ targetTerm) targetTerm := by
  cases typeEq
  cases rawEq
  rfl

/-- Transport a reducibility witness across a type-index equality whose
term side is cast by the symmetric equality.  This packages the exact
`Eq.rec` shape emitted by `TermSubst.singleton`. -/
theorem Reducible.of_type_eq_symm_cast
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {raw : RawTerm scope}
    (typeEq : sourceType = targetType)
    {targetTerm : Term context targetType raw}
    (targetReducible : Reducible targetType targetTerm) :
    Reducible sourceType (typeEq.symm ▸ targetTerm) := by
  cases typeEq
  exact targetReducible

/-- Transport a reducibility witness across a type-index equality whose
term side is cast by the equality itself. -/
theorem Reducible.of_type_eq_cast
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {raw : RawTerm scope}
    (typeEq : sourceType = targetType)
    {sourceTerm : Term context sourceType raw}
    (sourceReducible : Reducible sourceType sourceTerm) :
    Reducible targetType (typeEq ▸ sourceTerm) := by
  cases typeEq
  exact sourceReducible

/-- Transport a reducibility witness across a raw-index equality whose
term side is cast by the symmetric equality.  This is the raw-index
companion to `Reducible.of_type_eq_symm_cast`; it packages the exact
`Eq.rec` shape emitted by β-specific substitution extension. -/
theorem Reducible.of_raw_eq_symm_cast
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (rawEq : sourceRaw = targetRaw)
    {targetTerm : Term context sourceType targetRaw}
    (targetReducible : Reducible sourceType targetTerm) :
    Reducible sourceType (rawEq.symm ▸ targetTerm) := by
  cases rawEq
  exact targetReducible

/-- Transport a reducibility witness across a raw-index equality whose
term side is cast by the equality itself. -/
theorem Reducible.of_raw_eq_cast
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (rawEq : sourceRaw = targetRaw)
    {sourceTerm : Term context sourceType sourceRaw}
    (sourceReducible : Reducible sourceType sourceTerm) :
    Reducible sourceType (rawEq ▸ sourceTerm) := by
  cases rawEq
  exact sourceReducible

/-- Transport a reducibility witness across simultaneous type/raw
index equalities plus heterogeneous equality of the underlying typed
terms.

This is the general cast-wall helper needed by beta-contractum
transport: raw and type indices often align by separate substitution
laws, while the `Term` values themselves only align heterogeneously
because casts sit inside constructor arguments. -/
theorem Reducible.of_heq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (typeEq : sourceType = targetType)
    (rawEq : sourceRaw = targetRaw)
    (termHEq : HEq sourceTerm targetTerm)
    (sourceReducible : Reducible sourceType sourceTerm) :
    Reducible targetType targetTerm := by
  subst typeEq
  subst rawEq
  have termEq : sourceTerm = targetTerm := eq_of_heq termHEq
  subst termEq
  exact sourceReducible

end LeanFX2
