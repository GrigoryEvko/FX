import FX1Poly.Core.PolyCell

/-! # Foundation/PolyCell/Core/PolyCellHelpers — package helpers

This file ships convenience structures and constructors that
PACKAGE a certified `PolyCell` cell together with its sort, dim,
boundary, and rawCell indices into a single value.  These are the
"existentialized" wrappers the certifier (Stage L1c.4) and
downstream consumers use to pass certified cells around without
threading 5+ implicit arguments at every call site.

## The packaging problem

`PolyCell profile sort dim scope boundary rawCell` has 5 indices
in its type signature.  Code that wants to RETURN a certified cell
(e.g., the certifier) faces a choice:

* Existentially quantify each index: `Σ' sort, Σ' dim, Σ' rawCell,
  Σ' boundary, PolyCell ...`.  Verbose, hard to project from.

* Use a struct that bundles indices + cell into one named record.
  Each consumer projects via field accessors.  Clean.

This file ships the struct version, which is what `polycell.md` §4
indicates via its `CertifiedRawCellResult` type.  The v2 split is:

* `CertifiedCell` — the cell-only package (this file, #154).
* `CertifiedRawCellResult` — extends `CertifiedCell` with the
  input-code matching field needed by the certifier (Stage L1c.4,
  task #163).

## The `CertifiedCell` structure

Five fields:

```
structure CertifiedCell (profile : PolyProfile) (scope : Nat) where
  sort : CellSort
  dim : Nat
  rawCell : RawCell scope
  boundary : CellBoundary profile sort dim scope
  certifiedCell : PolyCell profile sort dim scope boundary rawCell
```

The `sort` and `dim` are not parameters because different cells in
the same packaging context can have different sort/dim.  Only
`profile` (fixed at compile time) and `scope` (fixed by the parent
context) stay as parameters.

## The four `package*` helpers

One per `PolyCell` constructor:

* `packageGen` — wraps a `gen` ctor application
* `packageGeneratingCell` — wraps a `generatingCell` ctor
* `packageVerticalComposite` — wraps a `verticalComposite` ctor
* `packageIdentityCell` — wraps an `identityCell` ctor

Each combines the ctor call with `CertifiedCell.ofCell` packaging.
Saves callers from threading the indices through both the ctor and
the package — they can just supply the ctor's arguments and get a
packaged result.

These mirror the spirit of v1's per-fixture builders
(`Core/Certified.lean:220-313`) but operate at the generic ctor
level rather than per-fixture.

## Zero-axiom verification

All declarations are propext-free: the structure is a plain
inductive (one constructor), the smart constructor and packaging
helpers are direct projections / ctor applications.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- A packaged certified cell.  Bundles the certified `PolyCell`
witness together with its sort, dim, boundary, and rawCell indices.

`profile` and `scope` are parameters (fixed across packaging
operations); `sort`, `dim`, `boundary`, `rawCell`, and `certifiedCell`
are fields (each cell can have different values).

The five fields are dependent: `boundary`'s type depends on
`sort, dim, scope`, and `certifiedCell`'s type depends on all the
prior fields.  Lean supports dependent records natively — the
projection accessors maintain the type chain. -/
structure CertifiedCell (profile : PolyProfile) (scope : Nat) where
  /-- The cell's sort (term / type / context / etc.). -/
  sort : CellSort
  /-- The cell's dimension. -/
  dim : Nat
  /-- The raw erasure (untyped form) of the cell. -/
  rawCell : RawCell scope
  /-- The cell's boundary index — Unit for dim 0, a source/target
  pair for dim n+1. -/
  boundary : CellBoundary profile sort dim scope
  /-- The certified cell itself, indexed by the four prior fields. -/
  certifiedCell : PolyCell profile sort dim scope boundary rawCell

namespace CertifiedCell

/-- Package a certified `PolyCell` cell into a `CertifiedCell`.

Mirrors v1's `CertifiedChild.ofCell` (`Core/Certified.lean:408`)
with the v2 vocabulary.  The implicit arguments are recovered from
the cell's type signature by Lean's unifier; callers just provide
the cell.

Usage: `CertifiedCell.ofCell cell` where `cell : PolyCell ...`. -/
def ofCell {profile : PolyProfile} {sort : CellSort}
    {dim scope : Nat}
    {boundary : CellBoundary profile sort dim scope}
    {rawCell : RawCell scope}
    (cell : PolyCell profile sort dim scope boundary rawCell) :
    CertifiedCell profile scope where
  sort := sort
  dim := dim
  rawCell := rawCell
  boundary := boundary
  certifiedCell := cell

end CertifiedCell

/-- Package a `gen` certified cell from its admission, payload
evidence, and certified spine.

Combines `PolyCell.gen` with `CertifiedCell.ofCell` in one
shot.  Returns the cell at sort `generator.cellSort`, dim 0, with
trivial boundary and raw erasure
`.termBase (.mkGen generator payload children)`. -/
def packageGen {profile : PolyProfile} {scope : Nat}
    {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (admission : SupportedGenerator generator)
    (payloadEvidence : GenPayloadEvidence generator scope payload)
    (childSpine : CertifiedTermSpine profile generator.childSpecs
                    scope generator.binderShifts children) :
    CertifiedCell profile scope :=
  CertifiedCell.ofCell
    (PolyCell.gen admission payloadEvidence childSpine)

/-- Package a `generatingCell` certified cell from its rule, admission,
endpoint cells, and dim-equality witness.

Combines `PolyCell.generatingCell` with `CertifiedCell.ofCell`.
Returns the cell at `source.dim + 1` with boundary
`(source, target)` and raw erasure
`.generatingCell rule.ruleId source target`.

The SPIKE-1 transport via `HasEqualDim` is propext-clean (decided
by `Nat.decEq` on `RawCell.dim`). -/
def packageGeneratingCell {profile : PolyProfile} {scope : Nat}
    (rule : RuleSpec)
    (admission : SupportedRuleSpec rule)
    {source target : RawCell scope}
    {sourceBoundary targetBoundary :
      CellBoundary profile rule.cellSort source.dim scope}
    (dimEq : HasEqualDim source target)
    (sourceCell : PolyCell profile rule.cellSort source.dim scope
                    sourceBoundary source)
    (targetCell : PolyCell profile rule.cellSort source.dim scope
                    targetBoundary target) :
    CertifiedCell profile scope :=
  CertifiedCell.ofCell
    (PolyCell.generatingCell rule admission dimEq sourceCell
      targetCell)

/-- Package a `verticalComposite` certified cell from two
component cells sharing a middle endpoint.

Combines `PolyCell.verticalComposite` with `CertifiedCell.ofCell`.
Returns the cell at `dim + 1` with boundary `(source, target)` and
raw erasure `.verticalComposite firstRaw secondRaw`. -/
def packageVerticalComposite {profile : PolyProfile}
    {sort : CellSort} {dim scope : Nat}
    {source middle target : RawCell scope}
    {firstRaw secondRaw : RawCell scope}
    (firstCell : PolyCell profile sort (dim + 1) scope
                   (CellBoundary.endpoints source middle) firstRaw)
    (secondCell : PolyCell profile sort (dim + 1) scope
                    (CellBoundary.endpoints middle target)
                    secondRaw) :
    CertifiedCell profile scope :=
  CertifiedCell.ofCell
    (PolyCell.verticalComposite firstCell secondCell)

/-- Package an `identityCell` from a certified base cell.

Combines `PolyCell.identityCell` with `CertifiedCell.ofCell`.
Returns the cell at `dim + 1` with boundary `(base, base)` and raw
erasure `.identityCell baseRaw`. -/
def packageIdentityCell {profile : PolyProfile} {sort : CellSort}
    {dim scope : Nat}
    {boundary : CellBoundary profile sort dim scope}
    {baseRaw : RawCell scope}
    (baseCell : PolyCell profile sort dim scope boundary baseRaw) :
    CertifiedCell profile scope :=
  CertifiedCell.ofCell (PolyCell.identityCell baseCell)

end FX1Poly.Core
