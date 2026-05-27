import LeanFX2.Foundation.PolyCell.Core.PolyCell
import LeanFX2.Foundation.PolyCell.Core.CellBoundary

/-! # Foundation/PolyCell/Core/CertifiedRawCell — raw-indexed certified package

This file ships `CertifiedRawCell`: the v2 analog of v1's
`CertifiedRawCell` (`Core/Certified.lean`).  It is a raw-INDEXED
certified package — like `CertifiedCell` (#154) but with the
`rawCell` as a TYPE PARAMETER, not a field.

## The two package types

* `CertifiedCell profile scope` — EXISTENTIAL.  rawCell is a
  field, varying per cell.  Used by `inferRawCellGeneral?` (#163)
  — the existential wrapper.

* `CertifiedRawCell profile scope rawCell` — RAW-INDEXED.
  rawCell is a parameter; the type pins the certificate to a
  specific raw input.  Used by `certifyRawCellExact?` (#162) —
  the recursive workhorse.

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

Three fields (vs CertifiedCell's five): `sort`, `boundary`,
`certifiedCell`.  The `dim` field is gone — replaced by `rawCell.dim`
(computed function on the parameter).  The `rawCell` field is also
gone — it's the type parameter.

## Why dim = rawCell.dim

In CertifiedCell the dim was an existential field (varied
per cell).  In CertifiedRawCell we KNOW the rawCell, so dim is
determined: it's `rawCell.dim` (the computed function from RawCell).

This commits the package to dimensional honesty — you can't
construct a CertifiedRawCell whose cell's dim differs from its
rawCell's dim.

## Zero-axiom verification

Pure structural dependent record.  Auto-derived projections + mk
constructor are all axiom-clean.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

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

end LeanFX2.Foundation.PolyCell.Core
