import LeanFX2.Reducibility.TypedCR2Direct

/-! # LeanFX2.Reducibility.TypedCR2Generic.GenericDispatch

Generic neutral / varShape CR3 dispatchers — uniform forms that
combine all per-Ty-arm CR3 closures from `TypedCR2Direct` and
dispatch on the outer Ty constructor.

* `Reducible.of_neutral_progress_closure` — generic neutral CR3.
* `Reducible.of_varShape` — variables-as-reducible.
* `IsRenamingStableReducible.of_varShape` — varShape stable under
  injective renamings.

## Root status

Layer 3 metatheory leaf.  First slice of `TypedCR2Generic`. -/

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

end LeanFX2
