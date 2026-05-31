import FX1Poly.Core.PolyCell
import FX1Poly.Core.CellBoundary

/-! # Foundation/PolyCell/Core/CertifiedRawCell — raw-indexed certified package

This file ships `CertifiedRawCell`: a raw-INDEXED certified
package — like `CertifiedCell` but with the `rawCell` as a TYPE
PARAMETER, not a field.

## The two package types

* `CertifiedCell profile scope` — EXISTENTIAL.  rawCell is a
  field, varying per cell.  Used by `inferRawCellGeneral?` —
  the existential wrapper.

* `CertifiedRawCell profile scope rawCell` — RAW-INDEXED.
  rawCell is a parameter; the type pins the certificate to a
  specific raw input.  Used by `certifyRawCellExact?` — the
  recursive workhorse.

Splitting the two clarifies the type-level guarantees: the exact
certifier never silently changes the rawCell it certifies, while
the existential wrapper is for callers who don't want to thread
the input rawCell through the return type.

## Field layout

```
structure CertifiedRawCell (profile : PolyProfile) (scope : Nat)
    (rawCell : RawCell scope) where
  sort : CellSort
  boundary : CellBoundary profile sort rawCell.dim scope
  certifiedCell : PolyCell profile sort rawCell.dim scope boundary rawCell
```

Three fields: `sort`, `boundary`, `certifiedCell`.  There is no
`dim` field — the dim is `rawCell.dim` (computed function on the
parameter).  There is no `rawCell` field — it's the type parameter.

## Why dim = rawCell.dim

Because the rawCell is KNOWN (a parameter), the dim is determined:
it's `rawCell.dim` (the computed function from RawCell).

This commits the package to dimensional honesty — you can't
construct a CertifiedRawCell whose cell's dim differs from its
rawCell's dim.

## Zero-axiom verification

Pure structural dependent record.  Auto-derived projections + mk
constructor are all axiom-clean.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- A certified cell pinned to a specific raw input.

`profile`, `scope`, and `rawCell` are PARAMETERS — fixed by the
caller.  `sort`, `boundary`, and `certifiedCell` are FIELDS —
projected via accessors.

The boundary's type uses `rawCell.dim` (a computed value), not an
existential dim field.  This means a CertifiedRawCell with
`rawCell := .termBase _` has boundary at dim 0 (Unit), while one
with `rawCell := .generatingCell ...` has boundary at dim source.dim+1
(a source/target pair). -/
structure CertifiedRawCell (profile : PolyProfile) (scope : Nat)
    (rawCell : RawCell scope) where
  /-- The cell's sort.  Differs per cell; the certifier picks it
  based on the rawCell's shape. -/
  sort : CellSort
  /-- The cell's boundary, typed at the computed `rawCell.dim`. -/
  boundary : CellBoundary profile sort rawCell.dim scope
  /-- The certified cell, indexed by sort, rawCell.dim, scope,
  boundary, and rawCell. -/
  certifiedCell :
    PolyCell profile sort rawCell.dim scope boundary rawCell

end FX1Poly.Core
