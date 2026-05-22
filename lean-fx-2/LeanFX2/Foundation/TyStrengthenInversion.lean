import LeanFX2.Foundation.TyStrengthen

/-! # Foundation/TyStrengthenInversion

Per-`Ty`-constructor inversion of `(Ty.<ctor> args).partialStrengthen?
back` from the composite `.isSome = true` to per-sub-component `.isSome =
true`.

Every `Ty` constructor with sub-`Ty` (or sub-`RawTerm`) fields defines
its `partialStrengthen?` via `Option.mapTwo` / `Option.mapThree` / a
direct `match`.  The composite succeeds iff every sub-field succeeds.
Inversion in the success direction is structurally trivial — case-split
on each sub-field's `partialStrengthen?`, discharge the impossible
`none` arms, and the `some` arms reduce by definition.

These inversion lemmas are consumed by the eventual universal
typed-strengthening driver (Block B `Step.par.preserves_rename_image`,
#2022): the per-arm `Term`-level wrappers in
`Term/StrengtheningImage/TargetImageTotality.lean` take per-sub-side
strengthening hypotheses as explicit inputs, and a structural-induction
driver over `Term` discharges those inputs from the global type-side
hypothesis via the lemmas in this file.

## Naming

* `partialStrengthen?_<ctor>_isSome` for the forward inversion.
* Each yields a conjunction (`∧`) of per-sub-field `.isSome = true`
  facts; binder cases use `back.lift` for the lifted sub-field.

## Tactics

`dsimp only [Ty.partialStrengthen?, Option.mapTwo, Option.mapThree]`
unfolds the constructor's definition to the underlying match, then a
`match` with witness extracts per-sub-field `partialStrengthen?` results
and discharges impossible cases via `cases`.  Zero axioms.
-/

namespace LeanFX2

namespace Ty

variable {level : Nat} {sourceScope targetScope : Nat}

/-- Inversion of `Ty.arrow` partial strengthening.

If a composite arrow type strengthens, both its domain and codomain
strengthen. -/
theorem partialStrengthen?_arrow_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (domainType codomainType : Ty level sourceScope)
    (composite :
      ((Ty.arrow domainType codomainType).partialStrengthen? back).isSome
        = true) :
    (domainType.partialStrengthen? back).isSome = true ∧
      (codomainType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match domainBranch : domainType.partialStrengthen? back with
    | none => rw [domainBranch] at composite; cases composite
    | some _ => rfl
  · match codomainBranch : codomainType.partialStrengthen? back with
    | none =>
        rw [codomainBranch] at composite
        match domainBranch : domainType.partialStrengthen? back with
        | none => rw [domainBranch] at composite; cases composite
        | some _ => rw [domainBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.piTy` partial strengthening.

If a composite dependent function type strengthens, the domain
strengthens (under `back`) and the codomain strengthens under the lifted
back-rename `back.lift` (since the codomain lives at `sourceScope + 1`). -/
theorem partialStrengthen?_piTy_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (domainType : Ty level sourceScope)
    (codomainType : Ty level (sourceScope + 1))
    (composite :
      ((Ty.piTy domainType codomainType).partialStrengthen? back).isSome
        = true) :
    (domainType.partialStrengthen? back).isSome = true ∧
      (codomainType.partialStrengthen? back.lift).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match domainBranch : domainType.partialStrengthen? back with
    | none => rw [domainBranch] at composite; cases composite
    | some _ => rfl
  · match codomainBranch : codomainType.partialStrengthen? back.lift with
    | none =>
        rw [codomainBranch] at composite
        match domainBranch : domainType.partialStrengthen? back with
        | none => rw [domainBranch] at composite; cases composite
        | some _ => rw [domainBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.sigmaTy` partial strengthening.

If a composite dependent pair type strengthens, the first component
strengthens (under `back`) and the second strengthens under the lifted
back-rename `back.lift` (since `secondType` lives at `sourceScope + 1`). -/
theorem partialStrengthen?_sigmaTy_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (firstType : Ty level sourceScope)
    (secondType : Ty level (sourceScope + 1))
    (composite :
      ((Ty.sigmaTy firstType secondType).partialStrengthen? back).isSome
        = true) :
    (firstType.partialStrengthen? back).isSome = true ∧
      (secondType.partialStrengthen? back.lift).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match firstBranch : firstType.partialStrengthen? back with
    | none => rw [firstBranch] at composite; cases composite
    | some _ => rfl
  · match secondBranch : secondType.partialStrengthen? back.lift with
    | none =>
        rw [secondBranch] at composite
        match firstBranch : firstType.partialStrengthen? back with
        | none => rw [firstBranch] at composite; cases composite
        | some _ => rw [firstBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.listType` partial strengthening.  Single-recursive
parametric container: the element type strengthens iff the composite
list type strengthens. -/
theorem partialStrengthen?_listType_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (elementType : Ty level sourceScope)
    (composite :
      ((Ty.listType elementType).partialStrengthen? back).isSome = true) :
    (elementType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?] at composite
  match elementBranch : elementType.partialStrengthen? back with
  | none => rw [elementBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `Ty.optionType` partial strengthening.  Single-recursive
parametric container: the element type strengthens iff the composite
option type strengthens. -/
theorem partialStrengthen?_optionType_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (elementType : Ty level sourceScope)
    (composite :
      ((Ty.optionType elementType).partialStrengthen? back).isSome
        = true) :
    (elementType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?] at composite
  match elementBranch : elementType.partialStrengthen? back with
  | none => rw [elementBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `Ty.eitherType` partial strengthening.  Both left and
right component types strengthen iff the composite either type
strengthens. -/
theorem partialStrengthen?_eitherType_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (leftType rightType : Ty level sourceScope)
    (composite :
      ((Ty.eitherType leftType rightType).partialStrengthen? back).isSome
        = true) :
    (leftType.partialStrengthen? back).isSome = true ∧
      (rightType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match leftBranch : leftType.partialStrengthen? back with
    | none => rw [leftBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightType.partialStrengthen? back with
    | none =>
        rw [rightBranch] at composite
        match leftBranch : leftType.partialStrengthen? back with
        | none => rw [leftBranch] at composite; cases composite
        | some _ => rw [leftBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.refine` partial strengthening.  The base type
strengthens under `back`; the predicate raw term strengthens under
`back.lift` (since the predicate lives at `sourceScope + 1`). -/
theorem partialStrengthen?_refine_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (baseType : Ty level sourceScope)
    (predicate : RawTerm (sourceScope + 1))
    (composite :
      ((Ty.refine baseType predicate).partialStrengthen? back).isSome
        = true) :
    (baseType.partialStrengthen? back).isSome = true ∧
      (predicate.partialStrengthen? back.lift).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match baseBranch : baseType.partialStrengthen? back with
    | none => rw [baseBranch] at composite; cases composite
    | some _ => rfl
  · match predicateBranch : predicate.partialStrengthen? back.lift with
    | none =>
        rw [predicateBranch] at composite
        match baseBranch : baseType.partialStrengthen? back with
        | none => rw [baseBranch] at composite; cases composite
        | some _ => rw [baseBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.codata` partial strengthening.  Both state and
output type components strengthen iff the composite codata type
strengthens. -/
theorem partialStrengthen?_codata_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (stateType outputType : Ty level sourceScope)
    (composite :
      ((Ty.codata stateType outputType).partialStrengthen? back).isSome
        = true) :
    (stateType.partialStrengthen? back).isSome = true ∧
      (outputType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match stateBranch : stateType.partialStrengthen? back with
    | none => rw [stateBranch] at composite; cases composite
    | some _ => rfl
  · match outputBranch : outputType.partialStrengthen? back with
    | none =>
        rw [outputBranch] at composite
        match stateBranch : stateType.partialStrengthen? back with
        | none => rw [stateBranch] at composite; cases composite
        | some _ => rw [stateBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.equiv` partial strengthening.  Both domain and
codomain components strengthen iff the composite equiv type
strengthens. -/
theorem partialStrengthen?_equiv_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (domainType codomainType : Ty level sourceScope)
    (composite :
      ((Ty.equiv domainType codomainType).partialStrengthen? back).isSome
        = true) :
    (domainType.partialStrengthen? back).isSome = true ∧
      (codomainType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match domainBranch : domainType.partialStrengthen? back with
    | none => rw [domainBranch] at composite; cases composite
    | some _ => rfl
  · match codomainBranch : codomainType.partialStrengthen? back with
    | none =>
        rw [codomainBranch] at composite
        match domainBranch : domainType.partialStrengthen? back with
        | none => rw [domainBranch] at composite; cases composite
        | some _ => rw [domainBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.modal` partial strengthening.  The carrier type
strengthens iff the composite modal type strengthens. -/
theorem partialStrengthen?_modal_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (modalityTag : Nat)
    (carrierType : Ty level sourceScope)
    (composite :
      ((Ty.modal modalityTag carrierType).partialStrengthen? back).isSome
        = true) :
    (carrierType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?] at composite
  match carrierBranch : carrierType.partialStrengthen? back with
  | none => rw [carrierBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `Ty.record` partial strengthening.  The single field
type strengthens iff the composite record type strengthens. -/
theorem partialStrengthen?_record_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (singleFieldType : Ty level sourceScope)
    (composite :
      ((Ty.record singleFieldType).partialStrengthen? back).isSome
        = true) :
    (singleFieldType.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?] at composite
  match fieldBranch : singleFieldType.partialStrengthen? back with
  | none => rw [fieldBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `Ty.session` partial strengthening.  The protocol step
raw term strengthens iff the composite session type strengthens. -/
theorem partialStrengthen?_session_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (protocolStep : RawTerm sourceScope)
    (composite :
      ((@Ty.session level sourceScope protocolStep).partialStrengthen?
        back).isSome = true) :
    (protocolStep.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?] at composite
  match protocolBranch : protocolStep.partialStrengthen? back with
  | none => rw [protocolBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `Ty.effect` partial strengthening.  Both the carrier
type and the effect tag raw term strengthen iff the composite effect
type strengthens. -/
theorem partialStrengthen?_effect_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (carrierType : Ty level sourceScope)
    (effectTag : RawTerm sourceScope)
    (composite :
      ((Ty.effect carrierType effectTag).partialStrengthen? back).isSome
        = true) :
    (carrierType.partialStrengthen? back).isSome = true ∧
      (effectTag.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match carrierBranch : carrierType.partialStrengthen? back with
    | none => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match effectBranch : effectTag.partialStrengthen? back with
    | none =>
        rw [effectBranch] at composite
        match carrierBranch : carrierType.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ => rw [carrierBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.glue` partial strengthening.  Both the base type
and the boundary witness raw term strengthen iff the composite glue
type strengthens. -/
theorem partialStrengthen?_glue_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (baseType : Ty level sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    (composite :
      ((Ty.glue baseType boundaryWitness).partialStrengthen? back).isSome
        = true) :
    (baseType.partialStrengthen? back).isSome = true ∧
      (boundaryWitness.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match baseBranch : baseType.partialStrengthen? back with
    | none => rw [baseBranch] at composite; cases composite
    | some _ => rfl
  · match boundaryBranch : boundaryWitness.partialStrengthen? back with
    | none =>
        rw [boundaryBranch] at composite
        match baseBranch : baseType.partialStrengthen? back with
        | none => rw [baseBranch] at composite; cases composite
        | some _ => rw [baseBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `Ty.id` partial strengthening.  The carrier type and
both endpoint raw terms strengthen iff the composite id type
strengthens. -/
theorem partialStrengthen?_id_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (carrier : Ty level sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    (composite :
      ((Ty.id carrier leftEndpoint rightEndpoint).partialStrengthen?
        back).isSome = true) :
    (carrier.partialStrengthen? back).isSome = true ∧
      (leftEndpoint.partialStrengthen? back).isSome = true ∧
      (rightEndpoint.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match carrierBranch : carrier.partialStrengthen? back with
    | none => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match leftBranch : leftEndpoint.partialStrengthen? back with
    | none =>
        rw [leftBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightEndpoint.partialStrengthen? back with
    | none =>
        rw [rightBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ =>
            match leftBranch : leftEndpoint.partialStrengthen? back with
            | none =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
            | some _ =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `Ty.path` partial strengthening.  The carrier type and
both endpoint raw terms strengthen iff the composite path type
strengthens. -/
theorem partialStrengthen?_path_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (carrier : Ty level sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    (composite :
      ((Ty.path carrier leftEndpoint rightEndpoint).partialStrengthen?
        back).isSome = true) :
    (carrier.partialStrengthen? back).isSome = true ∧
      (leftEndpoint.partialStrengthen? back).isSome = true ∧
      (rightEndpoint.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match carrierBranch : carrier.partialStrengthen? back with
    | none => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match leftBranch : leftEndpoint.partialStrengthen? back with
    | none =>
        rw [leftBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightEndpoint.partialStrengthen? back with
    | none =>
        rw [rightBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ =>
            match leftBranch : leftEndpoint.partialStrengthen? back with
            | none =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
            | some _ =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `Ty.oeq` partial strengthening.  The carrier type and
both endpoint raw terms strengthen iff the composite oeq type
strengthens. -/
theorem partialStrengthen?_oeq_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (carrier : Ty level sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    (composite :
      ((Ty.oeq carrier leftEndpoint rightEndpoint).partialStrengthen?
        back).isSome = true) :
    (carrier.partialStrengthen? back).isSome = true ∧
      (leftEndpoint.partialStrengthen? back).isSome = true ∧
      (rightEndpoint.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match carrierBranch : carrier.partialStrengthen? back with
    | none => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match leftBranch : leftEndpoint.partialStrengthen? back with
    | none =>
        rw [leftBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightEndpoint.partialStrengthen? back with
    | none =>
        rw [rightBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ =>
            match leftBranch : leftEndpoint.partialStrengthen? back with
            | none =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
            | some _ =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `Ty.idStrict` partial strengthening.  The carrier type
and both endpoint raw terms strengthen iff the composite strict-id
type strengthens. -/
theorem partialStrengthen?_idStrict_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (carrier : Ty level sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    (composite :
      ((Ty.idStrict carrier leftEndpoint rightEndpoint).partialStrengthen?
        back).isSome = true) :
    (carrier.partialStrengthen? back).isSome = true ∧
      (leftEndpoint.partialStrengthen? back).isSome = true ∧
      (rightEndpoint.partialStrengthen? back).isSome = true := by
  dsimp only [Ty.partialStrengthen?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match carrierBranch : carrier.partialStrengthen? back with
    | none => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match leftBranch : leftEndpoint.partialStrengthen? back with
    | none =>
        rw [leftBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ => rw [carrierBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightEndpoint.partialStrengthen? back with
    | none =>
        rw [rightBranch] at composite
        match carrierBranch : carrier.partialStrengthen? back with
        | none => rw [carrierBranch] at composite; cases composite
        | some _ =>
            match leftBranch : leftEndpoint.partialStrengthen? back with
            | none =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
            | some _ =>
                rw [carrierBranch, leftBranch] at composite
                cases composite
    | some _ => rfl

end Ty

end LeanFX2
