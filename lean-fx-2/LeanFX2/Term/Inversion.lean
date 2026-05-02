import LeanFX2.Term

/-! # Term/Inversion — typed Term inversions for unambiguous raw shapes

Phase 7.A scoped subject-reduction prep: inversion lemmas of the
form

```lean
Term ctx ty (RawTerm.<ctor> ...) → ty = <expected Ty shape>
```

where the raw shape uniquely determines the Term ctor — i.e. the
canonical-form heads (`.unit`, `.boolTrue`, …) and their
associated types.

## What's covered

* Nullary canonical heads: unit, boolTrue, boolFalse, natZero
* Unary unambiguous shapes: natSucc (always Ty.nat)
* Existential type shapes (with `∃ elementType`): listNil,
  listCons, optionNone, optionSome
* Unambiguous binary heads: eitherInl, eitherInr (with `∃
  leftType rightType`)

## What's NOT covered (deferred)

* lam / lamPi shape `.lam bodyRaw` is ambiguous — both ctors
  produce `RawTerm.lam` but at different types (`Ty.arrow` vs
  `Ty.piTy`).  Disambiguation needs the Ty's structure, not just
  the raw form.
* app / appPi shape `.app fnRaw argRaw` — same issue.
* fst / snd / pair — depend on the sigma type structure.
* refl — depends on identity-type structure.
* idJ — depends on motive type.
* boolElim / natElim / etc. — depend on motive type.

These will need richer inversion machinery (likely HEq-based
extraction of typed sub-components) — Phase 7 proper.

## Why this matters

Even the unambiguous-shape inversions are a structural building
block for the full subject-reduction theorem:

```lean
Step.par.fromRaw : Term ctx ty rawSource → RawStep.par rawSource rawTarget
                 → ∃ ty' targetTerm, Step.par sourceTerm targetTerm
```

For the cong cases that don't change type (most of them), the
inversion lets us extract typed sub-components and apply the
corresponding typed Step.par ctor.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- `Term ctx _ .unit` forces `ty = Ty.unit`. -/
theorem Term.unit_ty_inv
    {someType : Ty level scope}
    (someTerm : Term context someType (RawTerm.unit (scope := scope))) :
    someType = Ty.unit := by
  cases someTerm
  rfl

/-- `Term ctx _ .boolTrue` forces `ty = Ty.bool`. -/
theorem Term.boolTrue_ty_inv
    {someType : Ty level scope}
    (someTerm : Term context someType (RawTerm.boolTrue (scope := scope))) :
    someType = Ty.bool := by
  cases someTerm
  rfl

/-- `Term ctx _ .boolFalse` forces `ty = Ty.bool`. -/
theorem Term.boolFalse_ty_inv
    {someType : Ty level scope}
    (someTerm : Term context someType (RawTerm.boolFalse (scope := scope))) :
    someType = Ty.bool := by
  cases someTerm
  rfl

/-- `Term ctx _ .natZero` forces `ty = Ty.nat`. -/
theorem Term.natZero_ty_inv
    {someType : Ty level scope}
    (someTerm : Term context someType (RawTerm.natZero (scope := scope))) :
    someType = Ty.nat := by
  cases someTerm
  rfl

/-- `Term ctx _ (.natSucc _)` forces `ty = Ty.nat`. -/
theorem Term.natSucc_ty_inv
    {someType : Ty level scope}
    {predecessorRaw : RawTerm scope}
    (someTerm : Term context someType (RawTerm.natSucc predecessorRaw)) :
    someType = Ty.nat := by
  cases someTerm
  rfl

/-- `Term ctx _ .listNil` forces `ty = Ty.listType elementType` for
some `elementType`. -/
theorem Term.listNil_ty_inv
    {someType : Ty level scope}
    (someTerm : Term context someType (RawTerm.listNil (scope := scope))) :
    ∃ elementType, someType = Ty.listType elementType := by
  cases someTerm
  exact ⟨_, rfl⟩

/-- `Term ctx _ (.listCons _ _)` forces list type. -/
theorem Term.listCons_ty_inv
    {someType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (someTerm : Term context someType (RawTerm.listCons headRaw tailRaw)) :
    ∃ elementType, someType = Ty.listType elementType := by
  cases someTerm
  exact ⟨_, rfl⟩

/-- `Term ctx _ .optionNone` forces option type. -/
theorem Term.optionNone_ty_inv
    {someType : Ty level scope}
    (someTerm : Term context someType (RawTerm.optionNone (scope := scope))) :
    ∃ elementType, someType = Ty.optionType elementType := by
  cases someTerm
  exact ⟨_, rfl⟩

/-- `Term ctx _ (.optionSome _)` forces option type. -/
theorem Term.optionSome_ty_inv
    {someType : Ty level scope}
    {valueRaw : RawTerm scope}
    (someTerm : Term context someType (RawTerm.optionSome valueRaw)) :
    ∃ elementType, someType = Ty.optionType elementType := by
  cases someTerm
  exact ⟨_, rfl⟩

/-- `Term ctx _ (.eitherInl _)` forces either type. -/
theorem Term.eitherInl_ty_inv
    {someType : Ty level scope}
    {valueRaw : RawTerm scope}
    (someTerm : Term context someType (RawTerm.eitherInl valueRaw)) :
    ∃ leftType rightType, someType = Ty.eitherType leftType rightType := by
  cases someTerm
  exact ⟨_, _, rfl⟩

/-- `Term ctx _ (.eitherInr _)` forces either type. -/
theorem Term.eitherInr_ty_inv
    {someType : Ty level scope}
    {valueRaw : RawTerm scope}
    (someTerm : Term context someType (RawTerm.eitherInr valueRaw)) :
    ∃ leftType rightType, someType = Ty.eitherType leftType rightType := by
  cases someTerm
  exact ⟨_, _, rfl⟩

/-- `Term ctx _ (.refl rawWitness)` forces identity type with both
endpoints equal to `rawWitness`. -/
theorem Term.refl_ty_inv
    {someType : Ty level scope}
    {rawWitness : RawTerm scope}
    (someTerm : Term context someType (RawTerm.refl rawWitness)) :
    ∃ carrier, someType = Ty.id carrier rawWitness rawWitness := by
  cases someTerm
  exact ⟨_, rfl⟩

/-- `Term ctx _ (.pair _ _)` forces sigma type. -/
theorem Term.pair_ty_inv
    {someType : Ty level scope}
    {firstRaw secondRaw : RawTerm scope}
    (someTerm : Term context someType (RawTerm.pair firstRaw secondRaw)) :
    ∃ firstType secondType, someType = Ty.sigmaTy firstType secondType := by
  cases someTerm
  exact ⟨_, _, rfl⟩

/-! ## Uniqueness theorems for nullary canonical heads

Each nullary canonical-head Term ctor (`unit`, `boolTrue`,
`boolFalse`, `natZero`, `listNil`, `optionNone`) is uniquely
determined by its raw projection — given the context and the
raw form, there's exactly one Term value.  Proven via
`cases; cases; rfl`: each `cases` collapses both terms to the
matching ctor, then they're definitionally equal.

These theorems compose with the type inversions to give
"typed Conv between canonical heads is trivial" corollaries.
-/

/-- Two `Term ctx _ .unit` values are HEq. -/
theorem Term.unit_unique
    {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.unit (scope := scope)))
    (term2 : Term context ty2 (RawTerm.unit (scope := scope))) :
    HEq term1 term2 := by
  cases term1; cases term2; rfl

/-- Two `Term ctx _ .boolTrue` values are HEq. -/
theorem Term.boolTrue_unique
    {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.boolTrue (scope := scope)))
    (term2 : Term context ty2 (RawTerm.boolTrue (scope := scope))) :
    HEq term1 term2 := by
  cases term1; cases term2; rfl

/-- Two `Term ctx _ .boolFalse` values are HEq. -/
theorem Term.boolFalse_unique
    {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.boolFalse (scope := scope)))
    (term2 : Term context ty2 (RawTerm.boolFalse (scope := scope))) :
    HEq term1 term2 := by
  cases term1; cases term2; rfl

/-- Two `Term ctx _ .natZero` values are HEq. -/
theorem Term.natZero_unique
    {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.natZero (scope := scope)))
    (term2 : Term context ty2 (RawTerm.natZero (scope := scope))) :
    HEq term1 term2 := by
  cases term1; cases term2; rfl

/-- Two `Term ctx _ .listNil` values are HEq (forced equal element types). -/
theorem Term.listNil_unique
    {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.listNil (scope := scope)))
    (term2 : Term context ty2 (RawTerm.listNil (scope := scope))) :
    HEq term1 term2 ∨ ∃ elt1 elt2,
      ty1 = Ty.listType elt1 ∧ ty2 = Ty.listType elt2 := by
  -- listNil is parameterized by elementType; if the elementTypes
  -- differ between term1 and term2, they're at different types.
  cases term1; cases term2
  exact Or.inr ⟨_, _, rfl, rfl⟩

/-- Two `Term ctx _ .optionNone` values: parameterized by elementType. -/
theorem Term.optionNone_unique
    {ty1 ty2 : Ty level scope}
    (term1 : Term context ty1 (RawTerm.optionNone (scope := scope)))
    (term2 : Term context ty2 (RawTerm.optionNone (scope := scope))) :
    HEq term1 term2 ∨ ∃ elt1 elt2,
      ty1 = Ty.optionType elt1 ∧ ty2 = Ty.optionType elt2 := by
  cases term1; cases term2
  exact Or.inr ⟨_, _, rfl, rfl⟩

end LeanFX2
