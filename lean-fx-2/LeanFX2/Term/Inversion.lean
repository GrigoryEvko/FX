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

/-! ## Destructor for natSucc — propext-clean via free-the-index

Pattern: Lean 4 v4.29.1's `cases t` tactic on `t : Term context
Ty.nat (RawTerm.natSucc predRaw)` fails because the matcher
encounters non-natSucc cases (e.g., `Term.var pos`) and tries to
unify the TYPE first (`Ty.nat = varType context pos`), getting
stuck on the opaque `varType` projection.

Workaround per `feedback_lean_free_type_via_suffices.md`: free
the type index with `suffices`, then `cases t` runs on a generic
`ty` where the matcher discharges non-natSucc cases by RAW
contradiction (RawTerm.var pos ≠ RawTerm.natSucc predRaw is
constructor-mismatch, propext-clean).  The `ty = Ty.nat`
hypothesis is then used at the natSucc case to align indices.

Used to extend `Term.headStep?` for the `iotaNatElimSucc` /
`iotaNatRecSucc` cases — which need the predecessor to construct
the reduct `Term.app succBranch predecessor`. -/

/-- Destructor for `Term.natSucc`: from a typed Term at `Ty.nat`
whose raw form is `RawTerm.natSucc predRaw`, extract the
predecessor (a Term at `Ty.nat` with raw `predRaw`) bundled with
an HEq proof.  Zero-axiom via the suffices/free-index pattern. -/
def Term.natSuccDestruct
    {predRaw : RawTerm scope}
    (someTerm : Term context Ty.nat (RawTerm.natSucc predRaw)) :
    Σ' (predTerm : Term context Ty.nat predRaw),
       HEq someTerm (Term.natSucc predTerm) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.natSucc predRaw)),
        someType = Ty.nat →
        Σ' (predTerm : Term context Ty.nat predRaw),
           HEq genericTerm (Term.natSucc predTerm) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsNat
  cases genericTerm
  rename_i predTerm
  exact ⟨predTerm, HEq.rfl⟩

/-- Destructor for `Term.listCons`: from a typed Term at
`Ty.listType elementType` whose raw form is `RawTerm.listCons
headRaw tailRaw`, extract the head (a Term at elementType with
raw headRaw) and tail (a Term at listType with raw tailRaw)
bundled with an HEq proof. -/
def Term.listConsDestruct
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (someTerm : Term context (Ty.listType elementType)
                              (RawTerm.listCons headRaw tailRaw)) :
    Σ' (headTerm : Term context elementType headRaw)
       (tailTerm : Term context (Ty.listType elementType) tailRaw),
       HEq someTerm (Term.listCons headTerm tailTerm) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType
                                    (RawTerm.listCons headRaw tailRaw)),
        someType = Ty.listType elementType →
        Σ' (headTerm : Term context elementType headRaw)
           (tailTerm : Term context (Ty.listType elementType) tailRaw),
           HEq genericTerm (Term.listCons headTerm tailTerm) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsListType
  cases genericTerm
  rename_i innerElement headTerm tailTerm
  -- innerElement is the element type from the listCons ctor;
  -- the type-index hypothesis pins it to elementType
  have elementEq : innerElement = elementType :=
    Ty.listType.inj someTypeIsListType
  cases elementEq
  exact ⟨headTerm, tailTerm, HEq.rfl⟩

/-- Destructor for `Term.optionSome`: extract the value. -/
def Term.optionSomeDestruct
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (someTerm : Term context (Ty.optionType elementType)
                              (RawTerm.optionSome valueRaw)) :
    Σ' (valueTerm : Term context elementType valueRaw),
       HEq someTerm (Term.optionSome valueTerm) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.optionSome valueRaw)),
        someType = Ty.optionType elementType →
        Σ' (valueTerm : Term context elementType valueRaw),
           HEq genericTerm (Term.optionSome valueTerm) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsOpt
  cases genericTerm
  rename_i innerElement valueTerm
  have elementEq : innerElement = elementType :=
    Ty.optionType.inj someTypeIsOpt
  cases elementEq
  exact ⟨valueTerm, HEq.rfl⟩

/-- Destructor for `Term.eitherInl`: extract the left value. -/
def Term.eitherInlDestruct
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (someTerm : Term context (Ty.eitherType leftType rightType)
                              (RawTerm.eitherInl valueRaw)) :
    Σ' (valueTerm : Term context leftType valueRaw),
       HEq someTerm
           (Term.eitherInl (rightType := rightType) valueTerm) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.eitherInl valueRaw)),
        someType = Ty.eitherType leftType rightType →
        Σ' (valueTerm : Term context leftType valueRaw),
           HEq genericTerm
               (Term.eitherInl (rightType := rightType) valueTerm) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsEither
  cases genericTerm
  rename_i innerLeft innerRight valueTerm
  have eitherEq := Ty.eitherType.inj someTypeIsEither
  cases eitherEq.1
  cases eitherEq.2
  exact ⟨valueTerm, HEq.rfl⟩

/-- Destructor for `Term.eitherInr`: extract the right value. -/
def Term.eitherInrDestruct
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (someTerm : Term context (Ty.eitherType leftType rightType)
                              (RawTerm.eitherInr valueRaw)) :
    Σ' (valueTerm : Term context rightType valueRaw),
       HEq someTerm
           (Term.eitherInr (leftType := leftType) valueTerm) := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm : Term context someType (RawTerm.eitherInr valueRaw)),
        someType = Ty.eitherType leftType rightType →
        Σ' (valueTerm : Term context rightType valueRaw),
           HEq genericTerm
               (Term.eitherInr (leftType := leftType) valueTerm) by
    exact key someTerm rfl
  intro someType genericTerm someTypeIsEither
  cases genericTerm
  rename_i innerLeft innerRight valueTerm
  have eitherEq := Ty.eitherType.inj someTypeIsEither
  cases eitherEq.1
  cases eitherEq.2
  exact ⟨valueTerm, HEq.rfl⟩

/-! ## Raw-form recovery helpers — see `Algo/RawWHNF.lean`

When `Term.headStep?` dispatches via `scrutinee.headCtor`, it
gets a flat-enum tag but no Eq witness on `scrutinee.toRaw`.
The destructors above need raw-indexed terms — they require an
Eq proof.

Bridge helpers like `RawTerm.natSuccPred?_eq_some` recover the
raw form `term = RawTerm.natSucc predRaw` from a witness
`term.natSuccPred? = some predRaw`.  These live in
`Algo/RawWHNF.lean` next to the projection helpers themselves
(to keep the dependency direction clean — `Term/Inversion`
should not depend on `Algo`). -/

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
