import LeanFX2.Reducibility.TypedCR2Generic.GenericDispatch
import LeanFX2.Reducibility.TypedCR2Generic.HEqCasts

/-! # LeanFX2.Reducibility.TypedCR2Generic.SubstSingleton

`ReducibleSubst` singleton / cons-singleton / identity
constructors and their renaming-stability counterparts.  Covers
the post-rename composition lemma plus the four canonical
`ReducibleSubst` shapes.

## Root status

Layer 3 metatheory leaf.  Third slice of `TypedCR2Generic`. -/

namespace LeanFX2

/-- A renaming-stable substitution remains reducible after post-composing
its output with an injective typed renaming. -/
theorem ReducibleSubst.renameOutput_of_renamingStable
    {mode : Mode} {level sourceScope middleScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {middleCtx : Ctx mode level middleScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope middleScope}
    {rho : RawRenaming middleScope targetScope}
    {termSubst : TermSubst sourceCtx middleCtx sigma}
    (substIsStable : IsRenamingStableReducibleSubst termSubst)
    (rhoIsInjective : ∀ positionA positionB,
      rho positionA = rho positionB → positionA = positionB)
    (termRenaming : TermRenaming middleCtx targetCtx rho) :
    ReducibleSubst
      (TermSubst.renameOutput termSubst termRenaming) := by
  intro position
  change Reducible
    ((varType sourceCtx position).subst (Subst.renameOutput sigma rho))
    (Ty.subst_rename_commute sigma rho (varType sourceCtx position) ▸
      Term.rename termRenaming (termSubst position))
  exact Reducible.of_type_eq_cast
    (Ty.subst_rename_commute sigma rho (varType sourceCtx position))
    (substIsStable position rhoIsInjective termRenaming)

/-- **K12.20.U3 singleton ReducibleSubst**: replacing the newest
variable by a reducible argument yields a reducible singleton
substitution.

Position zero is the supplied reducible argument.  Older positions
survive `TermSubst.singleton` as variables in the target context, so
they are discharged by the all-type var-shape dispatcher. -/
theorem ReducibleSubst.singleton
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {substituent : Ty level scope}
    {argRaw : RawTerm scope}
    {argTerm : Term sourceCtx substituent argRaw}
    (argIsReducible : Reducible substituent argTerm) :
    ReducibleSubst (TermSubst.singleton argTerm) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          change Reducible
            (substituent.weaken.subst
              (Subst.singleton substituent argRaw))
            ((Ty.weaken_subst_singleton substituent substituent argRaw).symm ▸
              argTerm)
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_singleton substituent substituent argRaw)
            argIsReducible
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
          have previousVarReducible :
              Reducible (varType sourceCtx previousPosition)
                (Term.var previousPosition) :=
            Reducible.of_varShape
              (varType sourceCtx previousPosition)
              (Term.var previousPosition)
          change Reducible
            ((varType sourceCtx previousPosition).weaken.subst
              (Subst.singleton substituent argRaw))
            ((Ty.weaken_subst_singleton (varType sourceCtx previousPosition)
              substituent argRaw).symm ▸
                Term.var previousPosition)
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_singleton
              (varType sourceCtx previousPosition) substituent argRaw)
            previousVarReducible

/-- **K12.20.U3 singleton stability**: a singleton substitution is
renaming-stable when its substituted argument is renaming-stable.

Position zero transports the stable argument through the same
`Ty.weaken_subst_singleton` cast used by `TermSubst.singleton`; older
positions are casted variables and therefore use the var-shape
stability producer. -/
theorem IsRenamingStableReducibleSubst.singleton
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {substituent : Ty level scope}
    {argRaw : RawTerm scope}
    {argTerm : Term sourceCtx substituent argRaw}
    (argIsStable : IsRenamingStableReducible substituent argTerm) :
    IsRenamingStableReducibleSubst (TermSubst.singleton argTerm) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          change IsRenamingStableReducible
            (substituent.weaken.subst
              (Subst.singleton substituent argRaw))
            ((Ty.weaken_subst_singleton substituent substituent argRaw).symm ▸
              argTerm)
          intro targetScope targetCtx rho rhoIsInjective termRenaming
          have renamedArgIsReducible :
              Reducible (substituent.rename rho)
                (Term.rename termRenaming argTerm) :=
            argIsStable rhoIsInjective termRenaming
          have singletonTypeEq :
              substituent.weaken.subst
                (Subst.singleton substituent argRaw) = substituent :=
            Ty.weaken_subst_singleton substituent substituent argRaw
          have renamedCastIsHEq :
              HEq (Term.rename termRenaming argTerm)
                (Term.rename termRenaming (singletonTypeEq.symm ▸ argTerm)) := by
            have renamedCastToCastedArg :
                HEq
                  (Term.rename termRenaming (singletonTypeEq.symm ▸ argTerm))
                  ((congrArg (fun someType => Ty.rename someType rho)
                      singletonTypeEq).symm ▸
                    Term.rename termRenaming argTerm) :=
              Term.rename_type_eq_symm_cast_HEq termRenaming singletonTypeEq
            have castedArgToRenamedArg :
                HEq
                  ((congrArg (fun someType => Ty.rename someType rho)
                      singletonTypeEq).symm ▸
                    Term.rename termRenaming argTerm)
                  (Term.rename termRenaming argTerm) :=
              Term.type_eq_symm_cast_HEq
                (congrArg (fun someType => Ty.rename someType rho)
                  singletonTypeEq)
            exact (HEq.trans renamedCastToCastedArg
              castedArgToRenamedArg).symm
          exact Reducible.of_heq
            (congrArg (fun someType => Ty.rename someType rho)
              singletonTypeEq).symm
            rfl
            renamedCastIsHEq
            renamedArgIsReducible
      | succ previousIndex =>
          exact IsRenamingStableReducible.of_varShape rfl

/-- **K12.20.U3 cons-singleton stability**: extending a
renaming-stable substitution with a renaming-stable β argument yields a
renaming-stable substitution for the extended source context.

This is the stability companion to `ReducibleSubst.consSingleton`.
Position zero reuses the argument's stability through the
`Ty.weaken_subst_lift_singleton` cast.  Successor positions reuse the
old substitution entry's stability through the raw/type casts emitted
by `TermSubst.consSingleton`. -/
theorem IsRenamingStableReducibleSubst.consSingleton
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substIsStable : IsRenamingStableReducibleSubst termSubst)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (argumentIsStable :
      IsRenamingStableReducible (domainType.subst sigma) argumentTerm) :
    IsRenamingStableReducibleSubst
      (TermSubst.consSingleton termSubst argumentTerm) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          change IsRenamingStableReducible
            (domainType.weaken.subst
              (Subst.compose sigma.lift
                (Subst.singleton (domainType.subst sigma) argumentRaw)))
            ((Ty.weaken_subst_lift_singleton domainType domainType sigma
              argumentRaw).symm ▸ argumentTerm)
          intro renamedScope renamedCtx rho rhoIsInjective termRenaming
          have renamedArgumentIsReducible :
              Reducible ((domainType.subst sigma).rename rho)
                (Term.rename termRenaming argumentTerm) :=
            argumentIsStable rhoIsInjective termRenaming
          have typeEq :
              domainType.weaken.subst
                (Subst.compose sigma.lift
                  (Subst.singleton (domainType.subst sigma) argumentRaw)) =
                domainType.subst sigma :=
            Ty.weaken_subst_lift_singleton domainType domainType sigma
              argumentRaw
          have renamedCastIsHEq :
              HEq (Term.rename termRenaming argumentTerm)
                (Term.rename termRenaming (typeEq.symm ▸ argumentTerm)) := by
            have renamedCastToCastedArgument :
                HEq
                  (Term.rename termRenaming (typeEq.symm ▸ argumentTerm))
                  ((congrArg (fun someType => Ty.rename someType rho)
                      typeEq).symm ▸
                    Term.rename termRenaming argumentTerm) :=
              Term.rename_type_eq_symm_cast_HEq termRenaming typeEq
            have castedArgumentToRenamedArgument :
                HEq
                  ((congrArg (fun someType => Ty.rename someType rho)
                      typeEq).symm ▸
                    Term.rename termRenaming argumentTerm)
                  (Term.rename termRenaming argumentTerm) :=
              Term.type_eq_symm_cast_HEq
                (congrArg (fun someType => Ty.rename someType rho) typeEq)
            exact (HEq.trans renamedCastToCastedArgument
              castedArgumentToRenamedArgument).symm
          exact Reducible.of_heq
            (congrArg (fun someType => Ty.rename someType rho) typeEq).symm
            rfl
            renamedCastIsHEq
            renamedArgumentIsReducible
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
          have typeEq :
              ((varType (sourceCtx.cons domainType)
                  ⟨previousIndex + 1, positionIsWithinScope⟩).subst
                (Subst.compose sigma.lift
                  (Subst.singleton (domainType.subst sigma) argumentRaw))) =
                (varType sourceCtx previousPosition).subst sigma := by
            exact Ty.weaken_subst_lift_singleton
              (varType sourceCtx previousPosition) domainType sigma argumentRaw
          have rawEq :
              (Subst.compose sigma.lift
                  (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw
                  ⟨previousIndex + 1, positionIsWithinScope⟩ =
                sigma.forRaw previousPosition := by
            exact RawTerm.weaken_subst_singleton
              (sigma.forRaw previousPosition) argumentRaw
          change IsRenamingStableReducible
            ((varType (sourceCtx.cons domainType)
                ⟨previousIndex + 1, positionIsWithinScope⟩).subst
              (Subst.compose sigma.lift
                (Subst.singleton (domainType.subst sigma) argumentRaw)))
            (rawEq.symm ▸ typeEq.symm ▸ termSubst previousPosition)
          intro renamedScope renamedCtx rho rhoIsInjective termRenaming
          have renamedPreviousIsReducible :
              Reducible (((varType sourceCtx previousPosition).subst sigma).rename rho)
                (Term.rename termRenaming (termSubst previousPosition)) :=
            substIsStable previousPosition rhoIsInjective termRenaming
          have renamedCastToCastedPrevious :
              HEq
                (Term.rename termRenaming
                  (rawEq.symm ▸ typeEq.symm ▸ termSubst previousPosition))
                ((congrArg (fun someRaw => RawTerm.rename someRaw rho)
                    rawEq).symm ▸
                  (congrArg (fun someType => Ty.rename someType rho)
                    typeEq).symm ▸
                    Term.rename termRenaming (termSubst previousPosition)) :=
            Term.rename_raw_type_eq_symm_cast_HEq termRenaming typeEq rawEq
          have castedPreviousToRenamedPrevious :
              HEq
                ((congrArg (fun someRaw => RawTerm.rename someRaw rho)
                    rawEq).symm ▸
                  (congrArg (fun someType => Ty.rename someType rho)
                    typeEq).symm ▸
                    Term.rename termRenaming (termSubst previousPosition))
                (Term.rename termRenaming (termSubst previousPosition)) := by
            exact Term.raw_type_eq_symm_cast_HEq
              (congrArg (fun someType => Ty.rename someType rho) typeEq)
              (congrArg (fun someRaw => RawTerm.rename someRaw rho) rawEq)
          exact Reducible.of_heq
            (congrArg (fun someType => Ty.rename someType rho) typeEq).symm
            (congrArg (fun someRaw => RawTerm.rename someRaw rho) rawEq).symm
            (HEq.trans renamedCastToCastedPrevious
              castedPreviousToRenamedPrevious).symm
            renamedPreviousIsReducible

/-- **K12.20.U3 identity ReducibleSubst**: identity substitution is
reducible because every variable is reducible at its declared type. -/
theorem ReducibleSubst.identity
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    ReducibleSubst (TermSubst.identity sourceCtx) := by
  intro position
  have positionVarReducible :
      Reducible (varType sourceCtx position) (Term.var position) :=
    Reducible.of_varShape (varType sourceCtx position) (Term.var position)
  change Reducible
    ((varType sourceCtx position).subst Subst.identity)
    ((Ty.subst_identity (varType sourceCtx position)).symm ▸
      Term.var position)
  exact Reducible.of_type_eq_symm_cast
    (Ty.subst_identity (varType sourceCtx position))
    positionVarReducible

/-- **K12.20.U3 identity stability**: identity substitutions are
renaming-stable pointwise because each entry is a casted variable. -/
theorem IsRenamingStableReducibleSubst.identity
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    IsRenamingStableReducibleSubst (TermSubst.identity sourceCtx) := by
  intro position
  exact IsRenamingStableReducible.of_varShape rfl

end LeanFX2
