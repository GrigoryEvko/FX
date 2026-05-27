import LeanFX2.Foundation.PolyCell.Core.PolyCellV2

/-! # Foundation/PolyCell/Core/PolyCellV2Helpers — package helpers

This file ships convenience structures and constructors that
PACKAGE a certified `PolyCellV2` cell together with its sort, dim,
boundary, and rawCell indices into a single value.  These are the
"existentialized" wrappers the certifier (Stage L1c.4) and
downstream consumers use to pass certified cells around without
threading 5+ implicit arguments at every call site.

## The packaging problem

`PolyCellV2 profile sort dim scope boundary rawCell` has 5 indices
in its type signature.  Code that wants to RETURN a certified cell
(e.g., the certifier) faces a choice:

* Existentially quantify each index: `Σ' sort, Σ' dim, Σ' rawCell,
  Σ' boundary, PolyCellV2 ...`.  Verbose, hard to project from.

* Use a struct that bundles indices + cell into one named record.
  Each consumer projects via field accessors.  Clean.

This file ships the struct version, which is what `polycell.md` §4
indicates via its `CertifiedRawCellResult` type.  The v2 split is:

* `CertifiedCellV2` — the cell-only package (this file, #154).
* `CertifiedRawCellResultV2` — extends `CertifiedCellV2` with the
  input-code matching field needed by the certifier (Stage L1c.4,
  task #163).

## The `CertifiedCellV2` structure

Five fields:

```
structure CertifiedCellV2 (profile : PolyProfile) (scope : Nat) where
  sort : CellSort
  dim : Nat
  rawCell : RawCellV2 scope
  boundary : CellBoundaryV2 profile sort dim scope
  certifiedCell : PolyCellV2 profile sort dim scope boundary rawCell
```

The `sort` and `dim` are not parameters because different cells in
the same packaging context can have different sort/dim.  Only
`profile` (fixed at compile time) and `scope` (fixed by the parent
context) stay as parameters.

## The four `package*` helpers

One per `PolyCellV2` constructor:

* `packageGen` — wraps a `gen` ctor application
* `packageGeneratingCell` — wraps a `generatingCell` ctor
* `packageVerticalComposite` — wraps a `verticalComposite` ctor
* `packageIdentityCell` — wraps an `identityCell` ctor

Each combines the ctor call with `CertifiedCellV2.ofCell` packaging.
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

namespace LeanFX2.Foundation.PolyCell.Core

/-- A packaged certified cell.  Bundles the certified `PolyCellV2`
witness together with its sort, dim, boundary, and rawCell indices.

`profile` and `scope` are parameters (fixed across packaging
operations); `sort`, `dim`, `boundary`, `rawCell`, and `certifiedCell`
are fields (each cell can have different values).

The five fields are dependent: `boundary`'s type depends on
`sort, dim, scope`, and `certifiedCell`'s type depends on all the
prior fields.  Lean supports dependent records natively — the
projection accessors maintain the type chain. -/
structure CertifiedCellV2 (profile : PolyProfile) (scope : Nat) where
  /-- The cell's sort (term / type / context / etc.). -/
  sort : CellSort
  /-- The cell's dimension. -/
  dim : Nat
  /-- The raw erasure (untyped form) of the cell. -/
  rawCell : RawCellV2 scope
  /-- The cell's boundary index — Unit for dim 0, a source/target
  pair for dim n+1. -/
  boundary : CellBoundaryV2 profile sort dim scope
  /-- The certified cell itself, indexed by the four prior fields. -/
  certifiedCell : PolyCellV2 profile sort dim scope boundary rawCell

namespace CertifiedCellV2

/-- Package a certified `PolyCellV2` cell into a `CertifiedCellV2`.

Mirrors v1's `CertifiedChild.ofCell` (`Core/Certified.lean:408`)
with the v2 vocabulary.  The implicit arguments are recovered from
the cell's type signature by Lean's unifier; callers just provide
the cell.

Usage: `CertifiedCellV2.ofCell cell` where `cell : PolyCellV2 ...`. -/
def ofCell {profile : PolyProfile} {sort : CellSort}
    {dim scope : Nat}
    {boundary : CellBoundaryV2 profile sort dim scope}
    {rawCell : RawCellV2 scope}
    (cell : PolyCellV2 profile sort dim scope boundary rawCell) :
    CertifiedCellV2 profile scope where
  sort := sort
  dim := dim
  rawCell := rawCell
  boundary := boundary
  certifiedCell := cell

end CertifiedCellV2

/-- Package a `gen` certified cell from its admission, payload
evidence, and certified spine.

Combines `PolyCellV2.gen` with `CertifiedCellV2.ofCell` in one
shot.  Returns the cell at sort `generator.cellSort`, dim 0, with
trivial boundary and raw erasure
`.termBase (.mkGen generator payload children)`. -/
def packageGen {profile : PolyProfile} {scope : Nat}
    {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildrenV2 generator.binderShifts scope}
    (admission : SupportedGeneratorV2 generator)
    (payloadEvidence : GenPayloadEvidence generator scope payload)
    (childSpine : CertifiedTermSpineV2 profile generator.childSpecs
                    scope generator.binderShifts children) :
    CertifiedCellV2 profile scope :=
  CertifiedCellV2.ofCell
    (PolyCellV2.gen admission payloadEvidence childSpine)

/-- Package a `generatingCell` certified cell from its rule, admission,
endpoint cells, and dim-equality witness.

Combines `PolyCellV2.generatingCell` with `CertifiedCellV2.ofCell`.
Returns the cell at `source.dim + 1` with boundary
`(source, target)` and raw erasure
`.generatingCell rule.ruleId source target`.

The SPIKE-1 transport via `HasEqualDim` is propext-clean (decided
by `Nat.decEq` on `RawCellV2.dim`). -/
def packageGeneratingCell {profile : PolyProfile} {scope : Nat}
    (rule : RuleSpecV2)
    (admission : SupportedRuleSpecV2 rule)
    {source target : RawCellV2 scope}
    {sourceBoundary targetBoundary :
      CellBoundaryV2 profile rule.cellSort source.dim scope}
    (dimEq : HasEqualDim source target)
    (sourceCell : PolyCellV2 profile rule.cellSort source.dim scope
                    sourceBoundary source)
    (targetCell : PolyCellV2 profile rule.cellSort source.dim scope
                    targetBoundary target) :
    CertifiedCellV2 profile scope :=
  CertifiedCellV2.ofCell
    (PolyCellV2.generatingCell rule admission dimEq sourceCell
      targetCell)

/-- Package a `verticalComposite` certified cell from two
component cells sharing a middle endpoint.

Combines `PolyCellV2.verticalComposite` with `CertifiedCellV2.ofCell`.
Returns the cell at `dim + 1` with boundary `(source, target)` and
raw erasure `.verticalComposite firstRaw secondRaw`. -/
def packageVerticalComposite {profile : PolyProfile}
    {sort : CellSort} {dim scope : Nat}
    {source middle target : RawCellV2 scope}
    {firstRaw secondRaw : RawCellV2 scope}
    (firstCell : PolyCellV2 profile sort (dim + 1) scope
                   (CellBoundaryV2.endpoints source middle) firstRaw)
    (secondCell : PolyCellV2 profile sort (dim + 1) scope
                    (CellBoundaryV2.endpoints middle target)
                    secondRaw) :
    CertifiedCellV2 profile scope :=
  CertifiedCellV2.ofCell
    (PolyCellV2.verticalComposite firstCell secondCell)

/-- Package an `identityCell` from a certified base cell.

Combines `PolyCellV2.identityCell` with `CertifiedCellV2.ofCell`.
Returns the cell at `dim + 1` with boundary `(base, base)` and raw
erasure `.identityCell baseRaw`. -/
def packageIdentityCell {profile : PolyProfile} {sort : CellSort}
    {dim scope : Nat}
    {boundary : CellBoundaryV2 profile sort dim scope}
    {baseRaw : RawCellV2 scope}
    (baseCell : PolyCellV2 profile sort dim scope boundary baseRaw) :
    CertifiedCellV2 profile scope :=
  CertifiedCellV2.ofCell (PolyCellV2.identityCell baseCell)

end LeanFX2.Foundation.PolyCell.Core
