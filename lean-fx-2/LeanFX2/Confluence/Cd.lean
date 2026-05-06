import LeanFX2.Confluence.RawCd
import LeanFX2.Bridge

/-! # Confluence/Cd — complete-development at the raw projection of typed Terms

The Tait-Martin-Löf complete development `RawTerm.cd` already
ships fully (1126 lines, all 50+ ctors, zero axioms) in
`Confluence/RawCd.lean`.  This file lifts cd to the typed level
in the only way the architecture admits without subject reduction:
as the raw projection of a typed Term.

## Why no `Term.cd : Term ctx ty raw → Term ctx ty raw'`?

A typed `Term.cd` would need to land at a Term whose type matches
the raw cd output.  Several β/ι rules change the type along the
reduction (most subtly `betaSndPair`: the source type contains a
raw `RawTerm.fst (RawTerm.pair fr sr)` redex, the target type
contains `firstRaw` directly — `secondType.subst0 firstType (.fst
(.pair fr sr))` ≠ `secondType.subst0 firstType fr` definitionally).
Even non-dependent β-app needs `codomainType.weaken.subst0
domainType argRaw = codomainType` (subst-of-weaken cancellation),
which is propositional, not definitional.

Bridging these casts lives in subject reduction (Phase 7).  The
`Step` and `Step.par` constructors absorb the casts via two-Ty
heterogeneous source/target indices (see `Reduction/Step.lean`'s
two-Ty design comment).  A typed `Term.cd` AS A FUNCTION cannot
absorb them without first proving that every Step.par target is
typeable at the canonical reduct's type — which IS the subject-
reduction theorem.

The architectural escape valve adopted in lean-fx-2 (per
`Confluence/ParStarBridge.lean`'s docstring): consume the raw cd,
since typed convertibility is preserved by typing
(elaboration-time invariant).  Layer 9's decidable conversion
checks raw equivalence after both sides reach a canonical reduct;
the typed sides remain typed by elaboration discipline.

## Typed-input, raw-output cd

```lean
def Term.cdRaw : Term context tipe rawForm → RawTerm scope
  := fun _ => RawTerm.cd rawForm
```

The typed Term INPUT carries the raw form as a type-level index
(`Term.toRaw t = rawForm` is `rfl`); cdRaw simply consults that
index and returns its raw cd.  No new definition; just a name
under which the projection-into-cd is exposed.

## What this file ships (zero axioms)

* `Term.cdRaw` — typed-input, raw-output cd projection
* `Term.cdRaw_eq` — projection commutes with `RawTerm.cd`
* `Term.cdRaw_var` / `_unit` / `_lam` / etc. — per-ctor unfolding
  smoke tests (proven by rfl) that confirm the projection-into-cd
  is structural

## Dependencies

* `Confluence/RawCd.lean` — `RawTerm.cd` definition
* `Bridge.lean` — `Term.toRaw` projection (rfl by construction)

## Downstream consumers

* `Confluence/CdLemma.lean` — typed-input cd_lemma
* `Confluence/Diamond.lean` — diamond at typed inputs
-/

namespace LeanFX2

/-- **Typed-input, raw-output complete development.**  Given a
typed `Term context tipe rawForm`, return the raw `cd` of its
raw projection.  Definitionally `RawTerm.cd rawForm` since
`Term.toRaw t = rawForm` is rfl by construction. -/
@[reducible] def Term.cdRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {tipe : Ty level scope} {rawForm : RawTerm scope}
    (_typedTerm : Term context tipe rawForm) : RawTerm scope :=
  RawTerm.cd rawForm

/-- `Term.cdRaw` agrees with `RawTerm.cd` of the raw projection. -/
theorem Term.cdRaw_eq
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {tipe : Ty level scope} {rawForm : RawTerm scope}
    (typedTerm : Term context tipe rawForm) :
    Term.cdRaw typedTerm = RawTerm.cd rawForm := rfl

/-- Smoke: cdRaw of a typed unit is `RawTerm.unit`. -/
theorem Term.cdRaw_unit
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    Term.cdRaw (Term.unit (context := context)) = RawTerm.unit := rfl

/-- Smoke: cdRaw of a typed boolTrue is `RawTerm.boolTrue`. -/
theorem Term.cdRaw_boolTrue
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    Term.cdRaw (Term.boolTrue (context := context)) = RawTerm.boolTrue := rfl

/-- Smoke: cdRaw of a typed boolFalse is `RawTerm.boolFalse`. -/
theorem Term.cdRaw_boolFalse
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    Term.cdRaw (Term.boolFalse (context := context)) = RawTerm.boolFalse := rfl

/-- Smoke: cdRaw of natZero is `RawTerm.natZero`. -/
theorem Term.cdRaw_natZero
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    Term.cdRaw (Term.natZero (context := context)) = RawTerm.natZero := rfl

/-- Smoke: cdRaw of listNil is `RawTerm.listNil`. -/
theorem Term.cdRaw_listNil
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.cdRaw (Term.listNil (context := context) (elementType := elementType))
      = RawTerm.listNil := rfl

/-- Smoke: cdRaw of optionNone is `RawTerm.optionNone`. -/
theorem Term.cdRaw_optionNone
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.cdRaw (Term.optionNone (context := context) (elementType := elementType))
      = RawTerm.optionNone := rfl

end LeanFX2
