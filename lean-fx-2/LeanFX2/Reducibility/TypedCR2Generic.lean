import LeanFX2.Reducibility.TypedCR2Direct

/-! # LeanFX2.Reducibility.TypedCR2Generic — K12.20.U3 generic CR3 dispatch

The generic CR3 dispatch: a unified ~1500-LoC theorem that
combines all the per-Ty-arm CR3 closures from `TypedCR2Direct`
and dispatches on the outer Ty constructor.

## What ships

* `Reducible.cr3_generic` family — typed CR3 closure for every
  Reducible arm via dispatch.  Cases match the 25 Ty constructors
  and apply the appropriate per-arm CR3 lemma (`Reducible.cr3_X`)
  for each.
* Auxiliary generic dispatchers for the `_neutral` family
  (Reducible.X_of_neutral_progress_closure for ~10 compound arms).
* The Ty-cases match keeps full enumeration to avoid propext leak
  (per `feedback_lean_match_propext_recipe.md`).

## Root status

Layer 3 metatheory leaf.  Consumed by the typed Fundamental
modules for the var-case at every Ty arm. -/

namespace LeanFX2


/-! ### K12.20.U3 generic CR3 dispatch

The per-constructor K12.20.U2 arms above are the local proof
payloads.  Binder infrastructure needs one uniform dispatcher: given
an arbitrary neutral term at an arbitrary type, reduce by structural
recursion on `Ty` and pick the corresponding constructor arm. -/

/-- **K12.20.U3 neutral CR3 dispatcher**: every neutral term whose
non-trivial raw reducts are strongly normalizing is reducible at its
type.

This is the generic form consumed by `ReducibleSubst` constructors.
Compound arms recurse only into the strict sub-types that the current
K12 candidate actually exposes: codomain for arrow/equiv, first
projection for sigma, carrier/base/field/output for the projection
types.  SN-output arms (`piTy`, id-family, list/option/either) close
without recursive result-type calls. -/
theorem Reducible.of_neutral_progress_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    ∀ (sourceType : Ty level scope) {sourceRaw : RawTerm scope}
      (sourceTerm : Term context sourceType sourceRaw),
      RawTerm.IsNeutral sourceRaw →
      (∀ targetRaw : RawTerm scope,
        RawStep.parProgress sourceRaw targetRaw →
        RawTerm.isStronglyNormalizing targetRaw) →
      Reducible sourceType sourceTerm := by
  intro sourceType
  induction sourceType with
  | unit =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.unit_of_progress_closure sourceTerm closure
  | bool =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.bool_of_progress_closure sourceTerm closure
  | nat =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.nat_of_progress_closure sourceTerm closure
  | arrow domainType codomainType _domainIH codomainIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.arrow_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun codomainTerm codomainIsNeutral codomainClosure =>
          codomainIH codomainTerm codomainIsNeutral codomainClosure)
  | piTy domainType codomainType _domainIH _codomainIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.piTy_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
  | sigmaTy firstType secondType firstIH _secondIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.sigmaTy_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun firstTerm firstIsNeutral firstClosure =>
          firstIH firstTerm firstIsNeutral firstClosure)
  | tyVar position =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.tyVar_of_progress_closure sourceTerm closure
  | id carrier leftEndpoint rightEndpoint _carrierIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.id_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
  | listType elementType _elementIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.listType_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
  | optionType elementType _elementIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.optionType_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
  | eitherType leftType rightType _leftIH _rightIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.eitherType_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
  | «universe» universeLevel levelLe =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.universe_of_progress_closure sourceTerm closure
  | empty =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.empty_of_progress_closure sourceTerm closure
  | interval =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.interval_of_progress_closure sourceTerm closure
  | path carrier leftEndpoint rightEndpoint carrierIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.path_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun carrierTerm carrierIsNeutral carrierClosure =>
          carrierIH carrierTerm carrierIsNeutral carrierClosure)
  | glue baseType boundaryWitness baseIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.glue_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun baseTerm baseIsNeutral baseClosure =>
          baseIH baseTerm baseIsNeutral baseClosure)
  | oeq carrier leftEndpoint rightEndpoint _carrierIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.oeq_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
  | idStrict carrier leftEndpoint rightEndpoint _carrierIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.idStrict_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
  | equiv domainType codomainType _domainIH codomainIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.equiv_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun codomainTerm codomainIsNeutral codomainClosure =>
          codomainIH codomainTerm codomainIsNeutral codomainClosure)
  | refine baseType predicate baseIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.refine_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun baseTerm baseIsNeutral baseClosure =>
          baseIH baseTerm baseIsNeutral baseClosure)
  | record singleFieldType singleFieldIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.record_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun fieldTerm fieldIsNeutral fieldClosure =>
          singleFieldIH fieldTerm fieldIsNeutral fieldClosure)
  | codata stateType outputType _stateIH outputIH =>
      intro sourceRaw sourceTerm sourceIsNeutral closure
      exact Reducible.codata_of_neutral_progress_closure
        sourceTerm sourceIsNeutral closure
        (fun outputTerm outputIsNeutral outputClosure =>
          outputIH outputTerm outputIsNeutral outputClosure)
  | session protocolStep =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.session_of_progress_closure sourceTerm closure
  | effect carrierType effectTag _carrierIH =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.effect_of_progress_closure sourceTerm closure
  | modal modalityTag carrierType _carrierIH =>
      intro sourceRaw sourceTerm _sourceIsNeutral closure
      exact Reducible.modal_of_progress_closure sourceTerm closure

/-- **K12.20.U3 var-shape dispatcher**: variables are reducible at
every type. -/
theorem Reducible.of_varShape
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (sourceType : Ty level scope)
    {position : Fin scope}
    (sourceTerm : Term context sourceType (RawTerm.var position)) :
    Reducible sourceType sourceTerm :=
  Reducible.of_neutral_progress_closure sourceType sourceTerm
    (RawTerm.IsNeutral.var position)
    (fun targetRaw progressStep =>
      (RawTerm.var_has_no_progress position targetRaw progressStep).elim)

/-- Var-shaped reducibility is stable under every injective typed
renaming.

This is the CR3 producer for the Phase-B world-stability route:
renaming a raw variable remains a raw variable, and `Reducible.of_varShape`
already dispatches variables at every type. -/
theorem IsRenamingStableReducible.of_varShape
    {mode : Mode} {level sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {position : Fin sourceScope}
    (sourceRawEq : sourceRaw = RawTerm.var position) :
    IsRenamingStableReducible sourceType sourceTerm := by
  subst sourceRawEq
  intro _targetScope _targetCtx rho _rhoIsInjective termRenaming
  exact Reducible.of_varShape (sourceType.rename rho)
    (Term.rename termRenaming sourceTerm)

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

/-- **K12.20.U3.lift SN projection**: every entry of a lifted reducible
substitution is strongly normalizing.

This is the CR1 part of `ReducibleSubst.lift`, not the full theorem.
The fresh variable is SN by var-shape CR3; older positions are weakened
images of already-reducible substitution entries, so raw weakening
preserves their SN.  Compound `Reducible` closures remain the separate
world-monotone blocker tracked by #1944. -/
theorem ReducibleSubst.lift_isStronglyNormalizing
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substReducible : ReducibleSubst termSubst)
    (newSourceType : Ty level scope) :
    ∀ (position : Fin (scope + 1)),
      Term.isStronglyNormalizing
        ((termSubst.lift newSourceType) position) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          change RawTerm.isStronglyNormalizing
            (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩)
          exact RawTerm.var_isStronglyNormalizing
            ⟨0, Nat.zero_lt_succ targetScope⟩
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
          change Term.isStronglyNormalizing
            ((Ty.weaken_subst_commute sigma
              (varType sourceCtx previousPosition)).symm ▸
                Term.weaken (newSourceType.subst sigma)
                  (termSubst previousPosition))
          exact Term.isStronglyNormalizing_weaken
            (newType := newSourceType.subst sigma)
            (Reducible.isStronglyNormalizing
              (substReducible previousPosition))

/-- **K12.20.U3.lift under renaming stability**: a renaming-stable
reducible substitution lifts under one binder.

This is the first full-reducibility version of `ReducibleSubst.lift`.
The extra stability premise is the honest Kripke/world monotonicity
needed by old variables: after lifting, successor positions are exactly
the old substitution entries weakened into the extended target context.
Fresh position zero is a neutral variable and is reducible by CR3. -/
theorem ReducibleSubst.lift_of_renamingStable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substIsStable : IsRenamingStableReducibleSubst termSubst)
    (newSourceType : Ty level scope) :
    ReducibleSubst (termSubst.lift newSourceType) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_commute sigma newSourceType)
            (Reducible.of_varShape
              ((newSourceType.subst sigma).weaken)
              (Term.var (context := targetCtx.cons (newSourceType.subst sigma))
                ⟨0, Nat.zero_lt_succ targetScope⟩))
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex,
              Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
          change Reducible
            ((varType sourceCtx previousPosition).weaken.subst sigma.lift)
            ((Ty.weaken_subst_commute sigma
              (varType sourceCtx previousPosition)).symm ▸
                Term.weaken (newSourceType.subst sigma)
                  (termSubst previousPosition))
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_commute sigma
              (varType sourceCtx previousPosition))
            (IsRenamingStableReducibleSubst.weaken_position
              substIsStable newSourceType previousPosition)

/-- **K12.27.M04 identity-substitution SN extraction**.

The identity-only M04 route often proves SN for the term after
`TermSubst.identity`, because all fundamental endpoints are stated in
the substitution-parametric shape.  This lemma erases that identity
substitution from the raw index. -/
theorem Term.strong_normalization_of_identity_subst
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    (identityIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity sourceCtx) sourceTerm)) :
    Term.isStronglyNormalizing sourceTerm := by
  change RawTerm.isStronglyNormalizing sourceRaw
  rw [← RawTerm.subst_identity sourceRaw]
  exact identityIsSN

/-- **K12.27.M04 identity-substitution SN extraction**.

The final strong-normalization corollary will apply the fundamental
theorem at `TermSubst.identity`, then erase the identity substitution
from the raw index.  This lemma packages only that last extraction
step: it does not assert the still-pending fundamental theorem. -/
theorem Reducible.strong_normalization_of_identity_reducible
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (sourceTerm : Term sourceCtx sourceType sourceRaw)
    (identityReducible :
    Reducible (sourceType.subst Subst.identity)
        (Term.subst (TermSubst.identity sourceCtx) sourceTerm)) :
    Term.isStronglyNormalizing sourceTerm := by
  have identitySubstIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity sourceCtx) sourceTerm) :=
    Reducible.isStronglyNormalizing identityReducible
  exact Term.strong_normalization_of_identity_subst sourceTerm
    identitySubstIsSN

/-- **K12.27 identity-lift raw bridge**.

For the identity-only M04 route, the lambda body IH is naturally
available under `TermSubst.identity (sourceCtx.cons domainType)`, while
`Term.subst` on a lambda uses `(TermSubst.identity sourceCtx).lift`.
At the raw level those substitutions agree: lifting identity under one
binder is pointwise identity. -/
theorem RawTerm.subst_identity_lift
    {level scope : Nat}
    (sourceRaw : RawTerm (scope + 1)) :
    sourceRaw.subst ((@Subst.identity level scope).forRaw.lift) =
      sourceRaw := by
  rw [RawTerm.subst_pointwise
    (@Subst.identity_lift_forRaw_pointwise level scope) sourceRaw]
  exact RawTerm.subst_identity sourceRaw

/-- Strong normalization survives raw identity substitution. -/
theorem RawTerm.subst_identity_isStronglyNormalizing
    {level scope : Nat} {sourceRaw : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing sourceRaw) :
    RawTerm.isStronglyNormalizing
      (sourceRaw.subst (@Subst.identity level scope).forRaw) := by
  rw [RawTerm.subst_identity sourceRaw]
  exact sourceIsSN

/-- Strong normalization survives the lifted raw identity substitution
under one binder. -/
theorem RawTerm.subst_identity_lift_isStronglyNormalizing
    {level scope : Nat} {sourceRaw : RawTerm (scope + 1)}
    (sourceIsSN : RawTerm.isStronglyNormalizing sourceRaw) :
    RawTerm.isStronglyNormalizing
      (sourceRaw.subst ((@Subst.identity level scope).forRaw.lift)) := by
  rw [RawTerm.subst_identity_lift (level := level) (scope := scope)
    sourceRaw]
  exact sourceIsSN

/-- **K12.27 identity-lift body SN bridge**.

This is the lambda-specific identity-substitution bridge for the
M04-only route.  If the body is reducible under identity in the
extended context, then the body produced by substituting the enclosing
lambda with identity and entering its binder is strongly normalizing.

The result deliberately concludes only SN.  It does not provide generic
world-monotone `Reducible.weaken`; that stronger theorem remains the
full `ReducibleSubst.lift` blocker for non-identity substitutions. -/
theorem Reducible.identity_lift_body_sn_of_identity_reducible
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyIdentityReducible :
      Reducible (codomainType.weaken.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Ty.weaken_subst_commute Subst.identity codomainType ▸
        Term.subst ((TermSubst.identity sourceCtx).lift domainType)
          bodyTerm) := by
  have bodyIdentityIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm) :=
    Reducible.isStronglyNormalizing bodyIdentityReducible
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level scope).forRaw.lift))
  rw [RawTerm.subst_identity_lift (level := level) (scope := scope) bodyRaw]
  change RawTerm.isStronglyNormalizing bodyRaw
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level (scope + 1)).forRaw))
    at bodyIdentityIsSN
  rw [RawTerm.subst_identity bodyRaw] at bodyIdentityIsSN
  exact bodyIdentityIsSN

/-- **K12.27 generic identity-lift body SN bridge**.

This is the binder-generic form of
`identity_lift_body_sn_of_identity_reducible` for binders whose body
type already lives in the extended scope, such as `lamPi`.  The result
is still SN-only and identity-only; it deliberately does not claim
generic `ReducibleSubst.lift`. -/
theorem Reducible.identity_lift_body_sn_of_identity_reducible_at
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType : Ty level scope}
    {bodyType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (sourceCtx.cons domainType) bodyType bodyRaw}
    (bodyIdentityReducible :
      Reducible (bodyType.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst ((TermSubst.identity sourceCtx).lift domainType)
        bodyTerm) := by
  have bodyIdentityIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm) :=
    Reducible.isStronglyNormalizing bodyIdentityReducible
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level scope).forRaw.lift))
  rw [RawTerm.subst_identity_lift (level := level) (scope := scope) bodyRaw]
  change RawTerm.isStronglyNormalizing bodyRaw
  change RawTerm.isStronglyNormalizing
    (bodyRaw.subst ((@Subst.identity level (scope + 1)).forRaw))
    at bodyIdentityIsSN
  rw [RawTerm.subst_identity bodyRaw] at bodyIdentityIsSN
  exact bodyIdentityIsSN

/-- **K12.27 identity-substitution lambda value SN endpoint**.

This composes the identity-lift body bridge with the existing lambda
SN endpoint.  It is the identity-only counterpart of
`fundamental_lam_at_arrow_sn`: the body premise is the body IH under
`TermSubst.identity` in the extended context, not a generic lifted
substitution reducibility theorem. -/
theorem Reducible.fundamental_identity_lam_at_arrow_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyIdentityReducible :
      Reducible (codomainType.weaken.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Reducible.fundamental_lam_at_arrow_sn
    (termSubst := TermSubst.identity sourceCtx)
    (Reducible.identity_lift_body_sn_of_identity_reducible
      bodyIdentityReducible)

/-- **K12.20.U3 cons-singleton ReducibleSubst**: extending an existing
reducible substitution with a reducible β argument yields a reducible
substitution for the extended source context into the original target
context.

This is intentionally weaker and more specific than
`ReducibleSubst.lift`.  It is the substitution shape needed by the
lambda-body β contractum and does not require arbitrary
world-monotone weakening of old reducibility witnesses. -/
theorem ReducibleSubst.consSingleton
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    (substReducible : ReducibleSubst termSubst)
    {domainType : Ty level scope}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (argumentReducible : Reducible (domainType.subst sigma) argumentTerm) :
    ReducibleSubst
      (TermSubst.consSingleton termSubst argumentTerm) := by
  intro position
  cases position with
  | mk positionIndex positionIsWithinScope =>
      cases positionIndex with
      | zero =>
          change Reducible
            (domainType.weaken.subst
              (Subst.compose sigma.lift
                (Subst.singleton (domainType.subst sigma) argumentRaw)))
            ((Ty.weaken_subst_lift_singleton domainType domainType sigma
              argumentRaw).symm ▸ argumentTerm)
          exact Reducible.of_type_eq_symm_cast
            (Ty.weaken_subst_lift_singleton domainType domainType sigma
              argumentRaw)
            argumentReducible
      | succ previousIndex =>
          let previousPosition : Fin scope :=
            ⟨previousIndex, Nat.lt_of_succ_lt_succ positionIsWithinScope⟩
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
          change Reducible
            ((varType (sourceCtx.cons domainType)
                ⟨previousIndex + 1, positionIsWithinScope⟩).subst
              (Subst.compose sigma.lift
                (Subst.singleton (domainType.subst sigma) argumentRaw)))
            (rawEq.symm ▸ typeEq.symm ▸ termSubst previousPosition)
          exact Reducible.of_raw_eq_symm_cast rawEq
            (Reducible.of_type_eq_symm_cast typeEq
              (substReducible previousPosition))

/-- Full β-contractum reducibility bridge for the `Term.lam` arrow case,
assuming the typed substitution-composition HEq.

The body IH produces reducibility for `Term.subst` under
`TermSubst.consSingleton`.  The arrow application closure needs
reducibility of the concrete `Term.subst0` contractum produced from the
substituted lambda body.  Raw and type indices already align by the
β-specific substitution laws; the remaining non-definitional content is
the supplied Term-level HEq. -/
theorem Reducible.fundamental_lam_at_arrow_contractum
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (contractumHEq :
      HEq
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)
        (Term.subst0
          (Ty.weaken_subst_commute sigma codomainType ▸
            Term.subst (termSubst.lift domainType) bodyTerm)
          argumentTerm))
    (bodyContractumReducible :
      Reducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Reducible
      ((codomainType.subst sigma).weaken.subst0
        (domainType.subst sigma) argumentRaw)
      (Term.subst0
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm)
        argumentTerm) := by
  have typeEq :
      codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)) =
        (codomainType.subst sigma).weaken.subst0
          (domainType.subst sigma) argumentRaw := by
    exact (Ty.weaken_subst_lift_singleton codomainType domainType sigma
      argumentRaw).trans
        (Ty.weaken_subst_singleton (codomainType.subst sigma)
          (domainType.subst sigma) argumentRaw).symm
  have rawEq :
      bodyRaw.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)).forRaw =
        (bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw :=
    RawTerm.subst_lift_singleton_eq_subst0
      bodyRaw domainType sigma argumentRaw
  exact Reducible.of_heq typeEq rawEq contractumHEq
    bodyContractumReducible

/-- Lambda reducibility from the body IH under `consSingleton`, once the
typed β-contractum HEq is available.

This is the directly usable form of
`fundamental_lam_at_arrow_of_sn_codomain` for the Wood/Atkey lambda
case.  It keeps the two remaining obligations explicit:

* the lifted body is reducible at the weakened substituted codomain;
* each body contractum under `TermSubst.consSingleton` is HEq to the
  concrete `Term.subst0` target.

The body IH plus `ReducibleSubst.consSingleton` supplies
`bodyContractumReducible`; the missing cast-aware substitution theorem
supplies `bodyContractumHEq`. -/
theorem Reducible.fundamental_lam_at_arrow_of_consSingleton
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (bodyLiftReducible :
      Reducible ((codomainType.subst sigma).weaken)
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm))
    (bodyContractumHEq :
      ∀ {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw),
        HEq
          (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
            bodyTerm)
          (Term.subst0
            (Ty.weaken_subst_commute sigma codomainType ▸
              Term.subst (termSubst.lift domainType) bodyTerm)
            argumentTerm))
    (bodyContractumReducible :
      ∀ {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw),
        Reducible (domainType.subst sigma) argumentTerm →
        Reducible
          (codomainType.weaken.subst
            (Subst.compose sigma.lift
              (Subst.singleton (domainType.subst sigma) argumentRaw)))
          (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
            bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Reducible.fundamental_lam_at_arrow_of_sn_codomain
    codomainReducibleOfSN
    bodyLiftReducible
    (fun argumentTerm argumentReducible =>
      Reducible.fundamental_lam_at_arrow_contractum
        (bodyContractumHEq argumentTerm)
        (bodyContractumReducible argumentTerm argumentReducible))

/-- Lambda reducibility from the substitution-parametric body IH, modulo
the two remaining infrastructure blockers.

This theorem packages the Wood/Atkey lambda case up to:

* `liftSubstReducible`, the generic `ReducibleSubst.lift` obligation;
* `bodyContractumHEq`, the cast-aware β contractum substitution HEq;
* `codomainReducibleOfSN`, needed only for codomains whose candidate is
  recovered from SN at this frontier.

The body contractum side is no longer a blocker here: it is obtained by
calling the body IH under `TermSubst.consSingleton`, whose reducibility
is already supplied by `ReducibleSubst.consSingleton`. -/
theorem Reducible.fundamental_lam_at_arrow_of_bodyIH
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (substReducible : ReducibleSubst termSubst)
    (liftSubstReducible : ReducibleSubst (termSubst.lift domainType))
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm))
    (bodyContractumHEq :
      ∀ {argumentRaw : RawTerm targetScope}
        (argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw),
        HEq
          (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
            bodyTerm)
          (Term.subst0
            (Ty.weaken_subst_commute sigma codomainType ▸
              Term.subst (termSubst.lift domainType) bodyTerm)
            argumentTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  have bodyLiftReducible :
      Reducible ((codomainType.subst sigma).weaken)
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm) :=
    Reducible.of_type_eq_cast
      (Ty.weaken_subst_commute sigma codomainType)
      (bodyIH (termSubst.lift domainType) liftSubstReducible)
  exact Reducible.fundamental_lam_at_arrow_of_consSingleton
    codomainReducibleOfSN
    bodyLiftReducible
    bodyContractumHEq
    (fun argumentTerm argumentReducible =>
      bodyIH (TermSubst.consSingleton termSubst argumentTerm)
        (ReducibleSubst.consSingleton substReducible argumentReducible))

/-- β-contractum SN bridge for the `Term.lam` arrow case.

The body IH naturally applies to `TermSubst.consSingleton`, whose raw
substitution is `sigma.lift` composed with a singleton argument
substitution.  The application SN endpoint wants the equivalent
`Term.subst0` contractum of the lifted body.  This lemma is exactly
that raw-alignment bridge, demoted to the SN endpoint needed by M04. -/
theorem Reducible.fundamental_lam_at_arrow_contractum_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyContractumReducible :
      Reducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.subst0
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm)
        argumentTerm) := by
  have bodyContractumIsSN :
      Term.isStronglyNormalizing
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm) :=
    Reducible.isStronglyNormalizing bodyContractumReducible
  change RawTerm.isStronglyNormalizing
    ((bodyRaw.subst sigma.forRaw.lift).subst0 argumentRaw)
  rw [← RawTerm.subst_lift_singleton_eq_subst0
    bodyRaw domainType sigma argumentRaw]
  exact bodyContractumIsSN

/-- Combined SN endpoint for the `Term.lam` arrow application case.

This composes the three lambda SN pieces shipped so far:

* SN of the lifted body gives SN of the substituted lambda value.
* Reducibility of the argument gives SN of the argument.
* Reducibility of the body under `TermSubst.consSingleton` gives SN of
  the β-contractum aligned with `Term.subst0`.

The result is intentionally only the SN half of the arrow application
closure.  Full codomain `Reducible` still needs the separate
head-β/full-reducibility transport across the lifted-body cast. -/
theorem Reducible.fundamental_lam_at_arrow_app_sn_of_body_contractum
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    {argumentRaw : RawTerm targetScope}
    {argumentTerm : Term targetCtx (domainType.subst sigma) argumentRaw}
    (bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm))
    (argumentReducible : Reducible (domainType.subst sigma) argumentTerm)
    (bodyContractumReducible :
      Reducible
        (codomainType.weaken.subst
          (Subst.compose sigma.lift
            (Subst.singleton (domainType.subst sigma) argumentRaw)))
        (Term.subst (TermSubst.consSingleton termSubst argumentTerm)
          bodyTerm)) :
    Term.isStronglyNormalizing
      (Term.app
        (Term.subst termSubst
          (Term.lam (codomainType := codomainType) bodyTerm))
        argumentTerm) :=
  Reducible.fundamental_lam_at_arrow_app_sn bodyIsSN argumentReducible
    (Reducible.fundamental_lam_at_arrow_contractum_sn
      bodyContractumReducible)

/-- Lambda reducibility from the body IH for SN-recoverable codomains,
without the typed β-contractum HEq.

For codomains whose reducibility candidate can be rebuilt from strong
normalization, the arrow application closure only needs SN of the
β-redex.  That SN fact is already supplied by the raw-indexed
`fundamental_lam_at_arrow_app_sn_of_body_contractum` bridge from the
body IH under `TermSubst.consSingleton`; no typed contractum HEq is
needed on this narrower route. -/
theorem Reducible.fundamental_lam_at_arrow_of_bodyIH_sn_codomain
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (substReducible : ReducibleSubst termSubst)
    (liftSubstReducible : ReducibleSubst (termSubst.lift domainType))
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  have bodyLiftReducible :
      Reducible ((codomainType.subst sigma).weaken)
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm) :=
    Reducible.of_type_eq_cast
      (Ty.weaken_subst_commute sigma codomainType)
      (bodyIH (termSubst.lift domainType) liftSubstReducible)
  have bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute sigma codomainType ▸
          Term.subst (termSubst.lift domainType) bodyTerm) :=
    Reducible.isStronglyNormalizing bodyLiftReducible
  refine ⟨
    Reducible.fundamental_lam_at_arrow_sn
      (termSubst := termSubst)
      bodyIsSN,
    ?_⟩
  intro _argumentRaw argumentTerm argumentReducible
  exact codomainReducibleOfSN
    (Term.app
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm))
      argumentTerm)
    (Reducible.fundamental_lam_at_arrow_app_sn_of_body_contractum
      (termSubst := termSubst)
      bodyIsSN
      argumentReducible
      (bodyIH
        (TermSubst.consSingleton termSubst argumentTerm)
        (ReducibleSubst.consSingleton substReducible argumentReducible)))

/-- Lambda reducibility from a renaming-stable substitution and the body
IH, for SN-recoverable codomains.

This removes the explicit `liftSubstReducible` frontier premise from
`fundamental_lam_at_arrow_of_bodyIH_sn_codomain`: the lifted
substitution is now built by `ReducibleSubst.lift_of_renamingStable`.
The theorem is still honest about its scope: it only covers codomains
whose reducibility can be recovered from SN, and the full
substituted-codomain contractum reducibility route still needs the
typed β-contractum HEq. -/
theorem Reducible.fundamental_lam_at_arrow_of_stable_bodyIH_sn_codomain
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm targetScope}
        (resultTerm : Term targetCtx (codomainType.subst sigma) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst sigma) resultTerm)
    (substReducible : ReducibleSubst termSubst)
    (substIsStable : IsRenamingStableReducibleSubst termSubst)
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst sigma)
      (Term.subst termSubst
        (Term.lam (codomainType := codomainType) bodyTerm)) :=
  Reducible.fundamental_lam_at_arrow_of_bodyIH_sn_codomain
    codomainReducibleOfSN
    substReducible
    (ReducibleSubst.lift_of_renamingStable substIsStable domainType)
    bodyIH

/-- Identity-substitution lambda reducibility for SN-recoverable codomains.

This is the M04-facing specialization of
`fundamental_lam_at_arrow_of_bodyIH_sn_codomain`.  The value-SN side uses
the existing identity-lift bridge instead of generic
`ReducibleSubst.lift`; the application side still uses the body IH under
`TermSubst.consSingleton`, so reducible arguments feed the β-contractum
without requiring the typed β-contractum HEq. -/
theorem Reducible.fundamental_identity_lam_at_arrow_of_bodyIH_sn_codomain
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (codomainReducibleOfSN :
      ∀ {resultRaw : RawTerm scope}
        (resultTerm :
          Term sourceCtx (codomainType.subst Subst.identity) resultRaw),
        Term.isStronglyNormalizing resultTerm →
        Reducible (codomainType.subst Subst.identity) resultTerm)
    (bodyIH :
      ∀ {bodyTargetScope : Nat}
        {bodyTargetCtx : Ctx mode level bodyTargetScope}
        {bodySigma : Subst level (scope + 1) bodyTargetScope}
        (bodyTermSubst :
          TermSubst (sourceCtx.cons domainType) bodyTargetCtx bodySigma),
        ReducibleSubst bodyTermSubst →
        Reducible (codomainType.weaken.subst bodySigma)
          (Term.subst bodyTermSubst bodyTerm)) :
    Reducible ((Ty.arrow domainType codomainType).subst Subst.identity)
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := codomainType) bodyTerm)) := by
  have bodyIdentityReducible :
      Reducible (codomainType.weaken.subst Subst.identity)
        (Term.subst (TermSubst.identity (sourceCtx.cons domainType))
          bodyTerm) :=
    bodyIH (TermSubst.identity (sourceCtx.cons domainType))
      ReducibleSubst.identity
  have bodyIsSN :
      Term.isStronglyNormalizing
        (Ty.weaken_subst_commute Subst.identity codomainType ▸
          Term.subst ((TermSubst.identity sourceCtx).lift domainType)
            bodyTerm) :=
    Reducible.identity_lift_body_sn_of_identity_reducible
      bodyIdentityReducible
  refine ⟨
    Reducible.fundamental_lam_at_arrow_sn
      (termSubst := TermSubst.identity sourceCtx)
      bodyIsSN,
    ?_⟩
  intro _argumentRaw argumentTerm argumentReducible
  exact codomainReducibleOfSN
    (Term.app
      (Term.subst (TermSubst.identity sourceCtx)
        (Term.lam (codomainType := codomainType) bodyTerm))
      argumentTerm)
    (Reducible.fundamental_lam_at_arrow_app_sn_of_body_contractum
      (termSubst := TermSubst.identity sourceCtx)
      bodyIsSN
      argumentReducible
      (bodyIH
        (TermSubst.consSingleton
          (TermSubst.identity sourceCtx) argumentTerm)
        (ReducibleSubst.consSingleton
          ReducibleSubst.identity argumentReducible)))


end LeanFX2
