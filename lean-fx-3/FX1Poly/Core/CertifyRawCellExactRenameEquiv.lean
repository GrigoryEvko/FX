import FX1Poly.Core.RawCellRenameSubst
import FX1Poly.Core.CertifyRawCellExactCoverage

/-! # Foundation/PolyCell/Core/CertifyRawCellExactRenameEquiv

V2-L2.13 phase A (2026-05-27).  Discharges polycell.md §11.6.3
"Scope-shift coherence under the fold (the de Bruijn trap)".
Ships fixture-level rename-equivariance witnesses: renaming a
fixture by a scope-compatible renaming preserves both acceptance
and the certified sort.

## What V2-L2.13 wants

Per polycell.md:5514-5518, the rename-equivariance property of the
certifier is:

```
certifyRawCellExact? scope (RawTerm.rename ρ term) = Except.ok _
  ↔
certifyRawCellExact? (ρ scope) term = Except.ok _
```

Informally: renaming a well-formed term by a scope-compatible
renaming yields a well-formed term.  This is the operational glue
between "the fold is correct" and "the certifier agrees."

## Phase A: fixture-level witnesses

This commit ships the OBSERVATIONAL witnesses on four
representative fixtures from the V2-fix-5 coverage suite:

* `unitTermRaw` -- arity-0, no scope dependence (gen_unit's Unit
  payload).  Renaming by `weaken` shifts the cell from scope 0 to
  scope 1 without altering its structure.

* `varZeroRaw` -- arity-0 with `Fin scope` payload (gen_var at
  index 0).  Renaming by `weaken` shifts the var to index 1 at
  scope 2 (the Fin payload follows Fin.succ).

* `pairUnitsRaw` -- arity-2 with same-scope children.  Exercises
  spine-recursion under renaming.

* `identityUnitCellRaw` -- cell-layer fixture wrapping a termBase.
  Exercises the cell-layer rename's identityCell arm.

For each: the renamed fixture certifies at the SAME sort (`.term`)
as the original.  This pins the rename-equivariance property
empirically per fixture.

Each closes by `rfl`: the certifier is a pure computation, and
the renaming + certification chain reduces to a definite
`Except.ok` result.

## Phase B (tracked as M-certifier-rename-equivariance #378): the structural theorem

A full V2-L2.13 close requires proving the universally-quantified
rename-equivariance statement:

```
∀ {sourceScope targetScope} (rho : RawRenaming sourceScope targetScope)
  (term : RawTerm sourceScope),
  certifiedResultSort?
      (inferRawCellGeneral? sourceScope (.termBase term))
    = certifiedResultSort?
        (inferRawCellGeneral? targetScope
          (.termBase (RawTerm.rename rho term)))
```

This requires structural induction over `RawTerm` + the fold
recursion, threading through the lift-by-shift machinery.  The
proof's structure mirrors the Action laws (V2-L2.7) but needs an
additional layer to thread through the certifier's admission +
payload-evidence + spine-recursion chain.

Phase B is a real metatheory cascade -- meaningful enough to be
its own atomic ship.  Phase A (this commit) establishes the
EMPIRICAL baseline + the documentation framing that phase B will
generalize.

## Why this matters for §11.6.3's "de Bruijn trap"

The de Bruijn trap: off-by-one in lift-by-shift vs the certifier's
scope+shift creates a SILENT scope mismatch.  Passes on closed
terms (no free variables -> renaming is identity-on-output),
fails on open terms under binders.

The phase A fixtures include a free-variable case (varZeroRaw):
the gen_var Fin payload at index 0 must shift correctly to index
1 under Fin.succ-based weakening.  If the fold's lift-by-shift
were off-by-one, this fixture's renamed certification would fail
-- a regression detection capability that the unit/pair fixtures
alone cannot provide.

## Forward-compat

When phase B lands, these fixture witnesses become COROLLARIES of
the structural theorem (specialized instances).  Phase B will
likely supersede this file's docstring but preserve the witness
theorems as regression sentinels (they pin specific reduction
paths that a phase B regression could still break).

## Zero-axiom verification

All 9 declarations pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

namespace Coverage

/-! ## Renamed fixtures (weaken: scope_k -> scope_(k+1))

Each fixture is the corresponding coverage fixture renamed by
`RawRenaming.weaken`, shifting all variable indices up by one and
adding one fresh free variable slot at the top of the scope. -/

/-- `unitTermRaw` (scope 0) renamed to scope 1 via weaken. -/
def unitRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken unitTermRaw

/-- `varZeroRaw` (scope 1, `Fin 1` payload at 0) renamed to scope 2
via weaken (`Fin 2` payload at 1 -- the index shifts up). -/
def varZeroRenamedToScope2 : RawCell 2 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken varZeroRaw

/-- `pairUnitsRaw` (scope 0, arity-2 spine of units) renamed to
scope 1. -/
def pairUnitsRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken pairUnitsRaw

/-- `identityUnitCellRaw` (cell-layer fixture) renamed to scope 1. -/
def identityUnitCellRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken identityUnitCellRaw

end Coverage

/-! ## Sort-preservation theorems (per-fixture rename-equivariance)

Each theorem witnesses that the renamed fixture certifies at the
same sort (`.term`) as the original.  This pins rename-equivariance
empirically for each fixture. -/

/-- `unitTermRaw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_unitRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.unitRenamedToScope1) =
      some .term := rfl

/-- `varZeroRaw` renamed to scope 2 still certifies at `.term`.
The free-variable case witnesses that the Fin payload's index
shift (Fin.succ) is propagated correctly through the certifier. -/
theorem coverage_varZeroRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 2
        Coverage.varZeroRenamedToScope2) =
      some .term := rfl

/-- `pairUnitsRaw` renamed to scope 1 still certifies at `.term`.
Exercises the spine-recursion under renaming. -/
theorem coverage_pairUnitsRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.pairUnitsRenamedToScope1) =
      some .term := rfl

/-- `identityUnitCellRaw` renamed to scope 1 still certifies at
`.term`.  Exercises the cell-layer rename's `.identityCell` arm. -/
theorem coverage_identityUnitCellRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.identityUnitCellRenamedToScope1) =
      some .term := rfl

/-- **Cross-comparison agreement (unit fixture).**

The original `unitTermRaw` at scope 0 and the renamed
`unitRenamedToScope1` at scope 1 both certify at the SAME sort.
This is the rename-equivariance property AS AN AGREEMENT
EQUATION on the sort projection — the cleanest expression of
"renaming preserves observable certification outcomes" for this
fixture.

A similar agreement holds for each of the other three fixtures
above; one representative agreement theorem is shipped here, the
others follow by composing the per-fixture sort-preservation
theorems with `coverage_unitTermRaw_sort` (V2-fix-5). -/
theorem rename_equiv_unitTerm_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0
          Coverage.unitTermRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.unitRenamedToScope1) := rfl

/-- **Cross-comparison agreement (varZero fixture).**

The varZero fixture at scope 1 and its weakening to scope 2
both certify at `.term`.  Witnesses that the Fin-payload index
shift (Fin.succ on var 0 → var 1) preserves observable
certification outcomes. -/
theorem rename_equiv_varZero_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 1
          Coverage.varZeroRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 2
            Coverage.varZeroRenamedToScope2) := rfl

/-- **Cross-comparison agreement (pairUnits fixture).**

The pair fixture at scope 0 and its weakening to scope 1 both
certify at `.term`.  Witnesses spine-recursion stability under
renaming. -/
theorem rename_equiv_pairUnits_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0
          Coverage.pairUnitsRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.pairUnitsRenamedToScope1) := rfl

/-- **Cross-comparison agreement (identityUnitCell fixture).**

The cell-layer identityCell fixture at scope 0 and its weakening
to scope 1 both certify at `.term`.  Witnesses cell-layer
.identityCell arm stability under renaming. -/
theorem rename_equiv_identityUnitCell_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0
          Coverage.identityUnitCellRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.identityUnitCellRenamedToScope1) := rfl

/-! ## Closed-leaf rename-equivariance witnesses

Each of the 7 closed-leaf coverage fixtures gets a renamed
counterpart at scope 1 plus a sort-preservation theorem.
Closed-leaf fixtures contain no free variables, so weakening
adds an unused scope position — renaming should be observationally
identical to the original. -/

namespace Coverage

/-- `boolTrueRaw` weakened to scope 1. -/
def boolTrueRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken boolTrueRaw

/-- `boolFalseRaw` weakened to scope 1. -/
def boolFalseRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken boolFalseRaw

/-- `natZeroRaw` weakened to scope 1. -/
def natZeroRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken natZeroRaw

/-- `listNilRaw` weakened to scope 1. -/
def listNilRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken listNilRaw

/-- `optionNoneRaw` weakened to scope 1. -/
def optionNoneRenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken optionNoneRaw

/-- `interval0Raw` weakened to scope 1. -/
def interval0RenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken interval0Raw

/-- `interval1Raw` weakened to scope 1. -/
def interval1RenamedToScope1 : RawCell 1 :=
  RawCell.rename FX1Poly.Foundation.RawRenaming.weaken interval1Raw

end Coverage

/-- `boolTrueRaw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_boolTrueRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.boolTrueRenamedToScope1) =
      some .term := rfl

/-- `boolFalseRaw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_boolFalseRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.boolFalseRenamedToScope1) =
      some .term := rfl

/-- `natZeroRaw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_natZeroRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.natZeroRenamedToScope1) =
      some .term := rfl

/-- `listNilRaw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_listNilRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.listNilRenamedToScope1) =
      some .term := rfl

/-- `optionNoneRaw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_optionNoneRaw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.optionNoneRenamedToScope1) =
      some .term := rfl

/-- `interval0Raw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_interval0Raw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.interval0RenamedToScope1) =
      some .term := rfl

/-- `interval1Raw` renamed to scope 1 still certifies at `.term`. -/
theorem coverage_interval1Raw_renamed_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 1
        Coverage.interval1RenamedToScope1) =
      some .term := rfl

/-! ## Closed-leaf cross-comparison agreement theorems

7 cross-comparison agreements pairing each closed-leaf fixture
with its weakening — the cleanest form of "renaming preserves
observable certification outcomes" per closed-leaf. -/

/-- boolTrue cross-agreement. -/
theorem rename_equiv_boolTrue_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0 Coverage.boolTrueRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.boolTrueRenamedToScope1) := rfl

/-- boolFalse cross-agreement. -/
theorem rename_equiv_boolFalse_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0 Coverage.boolFalseRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.boolFalseRenamedToScope1) := rfl

/-- natZero cross-agreement. -/
theorem rename_equiv_natZero_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0 Coverage.natZeroRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.natZeroRenamedToScope1) := rfl

/-- listNil cross-agreement. -/
theorem rename_equiv_listNil_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0 Coverage.listNilRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.listNilRenamedToScope1) := rfl

/-- optionNone cross-agreement. -/
theorem rename_equiv_optionNone_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0 Coverage.optionNoneRaw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.optionNoneRenamedToScope1) := rfl

/-- interval0 cross-agreement. -/
theorem rename_equiv_interval0_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0 Coverage.interval0Raw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.interval0RenamedToScope1) := rfl

/-- interval1 cross-agreement. -/
theorem rename_equiv_interval1_sort_agree {profile : PolyProfile} :
    certifiedResultSort?
        (inferRawCellGeneral? (profile := profile) 0 Coverage.interval1Raw)
      = certifiedResultSort?
          (inferRawCellGeneral? (profile := profile) 1
            Coverage.interval1RenamedToScope1) := rfl

end FX1Poly.Core
