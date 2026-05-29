import FX1Poly.Core.InferRawCellGeneral

/-! # CertifyRawCellExactCoverage — positive-path acceptance suite

This file ships the positive-coverage suite for the v2 ingress: a
selection of fxProfile fixture raw cells along with `rfl`-proved
acceptance theorems demonstrating that the certifier ACCEPTS them
with the expected sort.

Direct v2 counterpart to v1's coverage suite at
`Core/CertifyExact.lean:113-126`.

## Why coverage matters alongside soundness

The L1cert.4 soundness tier (#165-#169) proves that the certifier
NEVER ACCEPTS BADLY — every accepted certification is faithful to
the input.  But soundness alone could be vacuously satisfied by a
certifier that ALWAYS REJECTS.

The coverage suite is the dual: every theorem here proves the
certifier ACCEPTS a specific well-formed fixture with the expected
sort.  Together, soundness + coverage establish that the certifier
is both correct (#165-#169) and useful (this file): it accepts the
things it should, and what it does on acceptance is correct.

## The fixture catalog

This file ships representative fixtures from the fxProfile generator
table.  Each fixture is the simplest well-formed instance of its
generator family:

* `unitTermRaw` — arity-0 `gen_unit` (Unit payload, sort `.term`)
* `varZeroRaw` — arity-0 `gen_var` at scope 1 (Fin payload, sort `.term`)

The catalog is intentionally minimal at this layer.  Per-generator
exhaustive coverage lives in downstream tasks; this layer
demonstrates the PATTERN and gates the certifier's `rfl`-evaluation
on concrete inputs.

## Why `rfl` works

Each acceptance theorem closes by `rfl` because the certifier is a
pure computation: given a closed RawCell input, it reduces via the
fuel wrapper + structural dispatch + admission lookup + payload
evidence + spine certification to a definite `Except.ok {...}` value.

Lean's `rfl` check unfolds:
1. `inferRawCellGeneral? scope raw` → matches on `certifyRawCellExact?`
2. The exact certifier dispatches on `raw`'s ctor (here always `.termBase`)
3. For `.termBase (.mkGen gen payload children)`:
   * `supportedGenerator? gen` reduces to `some <admission>`
   * `genPayloadEvidence? payload` reduces to `some <evidence>`
   * `certifyChildrenInlineFueled?` on `.childNil` reduces to `.ok .nil`
   * Returns `.ok { sort := generator.cellSort, ... }`
4. The wrapper packages this as `.ok { cellSort := generator.cellSort, ... }`
5. `certifiedResultSort?` projects `.cellSort = generator.cellSort`

All reductions are definitional under v2's structural definitions.

## Zero-axiom verification

All declarations propext-free:
* Fixture raw cells are pure data (struct construction)
* Acceptance theorems close by `rfl`
* The `certifiedResultSort?` helper is a one-line `def` matching
  on Except

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- Extract the sort from an accepted certified-result computation.

Mirrors v1's `certifiedResultSort?` (`Core/Check.lean:2115`).  Used
by coverage theorems to inspect the certifier's output sort without
unpacking the full result struct. -/
def certifiedResultSort? {profile : PolyProfile} {scope : Nat} :
    Except CellCheckRejection (CertifiedRawCellResult profile scope) →
      Option CellSort
  | Except.ok result => some result.cellSort
  | Except.error _ => none

namespace Coverage

/-- The simplest dim-0 fxProfile fixture: a `unit` term with empty
children spine at scope 0.

  `unitTermRaw = .termBase (.mkGen .gen_unit () .childNil)`

`gen_unit` is arity-0 (no children), payload `Unit` (the single
inhabitant `()`), sort `.term`, cellDimension 0.  This is the
minimal acceptance test for the dim-0 term ingress. -/
def unitTermRaw : RawCell 0 :=
  .termBase (.mkGen .gen_unit () .childNil)

/-- A second dim-0 fixture exercising a non-trivial payload: the
variable `0` at scope 1.

  `varZeroRaw = .termBase (.mkGen .gen_var ⟨0, _⟩ .childNil)`

`gen_var` is arity-0 (no children), payload `Fin scope` (here
`Fin 1` = single inhabitant), sort `.term`, cellDimension 0.  This
exercises the `Fin scope` payload-evidence path. -/
def varZeroRaw : RawCell 1 :=
  .termBase (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)

/-! ## V2-fix-5: arity-0 generator fixtures (boolean + naturals + lists + options + interval)

Each `gen_X_Raw` is the simplest well-formed instance of an arity-0
generator family.  All certify at sort `.term`, cellDimension 0
under fxProfile.  Each exercises a distinct `Generator` ctor through
the certifier's admission + payload-evidence + nil-spine chain. -/

/-- Arity-0 fixture: boolean `true`. -/
def boolTrueRaw : RawCell 0 :=
  .termBase (.mkGen .gen_boolTrue () .childNil)

/-- Arity-0 fixture: boolean `false`. -/
def boolFalseRaw : RawCell 0 :=
  .termBase (.mkGen .gen_boolFalse () .childNil)

/-- Arity-0 fixture: natural number `0`. -/
def natZeroRaw : RawCell 0 :=
  .termBase (.mkGen .gen_natZero () .childNil)

/-- Arity-0 fixture: empty list. -/
def listNilRaw : RawCell 0 :=
  .termBase (.mkGen .gen_listNil () .childNil)

/-- Arity-0 fixture: option `none`. -/
def optionNoneRaw : RawCell 0 :=
  .termBase (.mkGen .gen_optionNone () .childNil)

/-- Arity-0 fixture: cubical interval endpoint `0`. -/
def interval0Raw : RawCell 0 :=
  .termBase (.mkGen .gen_interval0 () .childNil)

/-- Arity-0 fixture: cubical interval endpoint `1`. -/
def interval1Raw : RawCell 0 :=
  .termBase (.mkGen .gen_interval1 () .childNil)

/-! ## V2-fix-5: arity-1+ generator fixtures (compositional shapes)

These fixtures exercise the certifier's children-spine recursion
through arity-1 and arity-2 generators with concrete sub-fixtures. -/

/-- Arity-1 fixture: `natSucc natZero` = the natural number `1`.
Exercises the children-spine path through one recursion level. -/
def natSuccZeroRaw : RawCell 0 :=
  .termBase (.mkGen .gen_natSucc ()
    (.childCons (.mkGen .gen_natZero () .childNil) .childNil))

/-- Arity-1 fixture: `optionSome unit` = an option holding unit.
Exercises the spine path through option's container. -/
def optionSomeUnitRaw : RawCell 0 :=
  .termBase (.mkGen .gen_optionSome ()
    (.childCons (.mkGen .gen_unit () .childNil) .childNil))

/-- Arity-1 fixture: `eitherInl unit` = a left-tagged either of unit.
Exercises the spine path through either's left injection. -/
def eitherInlUnitRaw : RawCell 0 :=
  .termBase (.mkGen .gen_eitherInl ()
    (.childCons (.mkGen .gen_unit () .childNil) .childNil))

/-- Arity-2 fixture: `pair unit unit` = the pair `(unit, unit)`.
Exercises the spine path through two adjacent same-scope children. -/
def pairUnitsRaw : RawCell 0 :=
  .termBase (.mkGen .gen_pair ()
    (.childCons (.mkGen .gen_unit () .childNil)
      (.childCons (.mkGen .gen_unit () .childNil) .childNil)))

/-- Arity-2 fixture: `listCons unit listNil` = a one-element list
holding unit.  Exercises a heterogeneous spine: an arbitrary head
+ a list-typed tail. -/
def listConsUnitRaw : RawCell 0 :=
  .termBase (.mkGen .gen_listCons ()
    (.childCons (.mkGen .gen_unit () .childNil)
      (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))

/-! ## V2-fix-5: cell-layer fixture (dim 1 via identityCell)

This fixture exercises the certifier's CELL-LAYER dispatch arms,
distinct from the term-layer arms covered by the termBase fixtures
above. -/

/-- Cell-layer fixture: `identityCell unitTerm` = the identity cell on
the unit term, a dim-1 cell with both endpoints equal to the unit
term.  Exercises the identityCell branch of `certifyRawCellExact?`. -/
def identityUnitCellRaw : RawCell 0 :=
  .identityCell (.termBase (.mkGen .gen_unit () .childNil))

end Coverage

/-- The `unitTerm` fixture certifies at sort `.term` through the
general existential ingress.

Closes by `rfl`: the entire `inferRawCellGeneral? 0 unitTermRaw`
chain reduces to `.ok {..cellSort := .term..}` via the certifier's
admission + payload-evidence + nil-spine + packaging steps. -/
theorem coverage_unitTermRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.unitTermRaw) =
      some .term := rfl

/-- The `varZero` fixture certifies at sort `.term` through the
general existential ingress.

Closes by `rfl`: exercises the `gen_var`'s `Fin scope` payload
path, distinct from `gen_unit`'s `Unit` path.  Both certify cleanly
at sort `.term`. -/
theorem coverage_varZeroRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.varZeroRaw) =
      some .term := rfl

/-! ## V2-fix-5: acceptance theorems for the expanded fixture set

Thirteen new fixture theorems extending the certifier's `rfl`-evaluation
coverage from 2 fixtures to 15.  Each closes by `rfl` because the
certifier is a pure computation reducing fixtures through the
admission + payload-evidence + spine-recursion chain.

Together with `coverage_unitTermRaw_sort` and `coverage_varZeroRaw_sort`,
the catalog now spans:

* **Arity 0**: gen_unit, gen_var, gen_boolTrue, gen_boolFalse,
  gen_natZero, gen_listNil, gen_optionNone, gen_interval0, gen_interval1
  (9 distinct generators, all sort `.term`).
* **Arity 1**: gen_natSucc, gen_optionSome, gen_eitherInl (3 distinct
  generators exercising one-level recursion).
* **Arity 2**: gen_pair, gen_listCons (2 generators exercising
  two-element spine recursion).
* **Cell layer**: identityCell wrapping a termBase (1 dim-1 cell). -/

theorem coverage_boolTrueRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.boolTrueRaw) =
      some .term := rfl

theorem coverage_boolFalseRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.boolFalseRaw) =
      some .term := rfl

theorem coverage_natZeroRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.natZeroRaw) =
      some .term := rfl

theorem coverage_listNilRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.listNilRaw) =
      some .term := rfl

theorem coverage_optionNoneRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.optionNoneRaw) =
      some .term := rfl

theorem coverage_interval0Raw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.interval0Raw) =
      some .term := rfl

theorem coverage_interval1Raw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.interval1Raw) =
      some .term := rfl

theorem coverage_natSuccZeroRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.natSuccZeroRaw) =
      some .term := rfl

theorem coverage_optionSomeUnitRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.optionSomeUnitRaw) =
      some .term := rfl

theorem coverage_eitherInlUnitRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.eitherInlUnitRaw) =
      some .term := rfl

theorem coverage_pairUnitsRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.pairUnitsRaw) =
      some .term := rfl

theorem coverage_listConsUnitRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.listConsUnitRaw) =
      some .term := rfl

theorem coverage_identityUnitCellRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0
        Coverage.identityUnitCellRaw) =
      some .term := rfl

end FX1Poly.Core
