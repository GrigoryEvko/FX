import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneral

/-! # InferRawCellGeneralAcceptedCellDimensionEq — existential preserves dim

This file ships `inferRawCellGeneral?_accepted_cellDimension_eq`:
the first of three existential-variant soundness theorems for the
ingress.  When the existential wrapper accepts a raw input, the
result's stored `cellDimension` field equals the input's structural
dim (`raw.dim`).

Direct v2 counterpart to v1's
`inferRawCellGeneral?_accepted_cellDimension_eq`
(`Core/CertifyExact.lean:155`).

## Why this theorem matters

The existential wrapper `inferRawCellGeneral?` returns a
`CertifiedRawCellResult` whose `cellDimension` is a FIELD (not a
type parameter).  Without a separate soundness witness, the wrapper
COULD in principle launder a different dim past the input — return
a result whose `cellDimension` doesn't match the raw cell's
structural dim.

This theorem rules that out: every accepted call's result has
`cellDimension = raw.dim`.

Together with #168 (`_accepted_rawCell_heq`, the raw equality) and
#169 (`_sound`, the HEq composition), this closes the
no-laundering guarantee on the existential ingress.

## The proof shape

Standard "executable-soundness" pattern, three steps:

1. **Unfold** `inferRawCellGeneral?` in the hypothesis to expose
   the underlying `match certifyRawCellExact? ... with`.
2. **Case** on the underlying `certifyRawCellExact?` result via
   `cases h : ... with`, capturing the equation `h` for each branch.
3. **In error branch**: the unfolded `accepted` becomes
   `Except.error _ = Except.ok result`, contradiction via `cases`.
   **In ok branch**: the unfolded `accepted` becomes
   `Except.ok {...with cellDimension := raw.dim...} = Except.ok result`.
   `injection` extracts the equation; `subst` substitutes;
   `rfl` closes (the struct projection reduces).

## Zero-axiom verification

All tactics are propext-free:
* `rw` with the function name uses Eq.ndrec (definitional rewriting)
* `cases h : expr with` introduces equation hypothesis
* `injection` on the inductive's constructor (Except.ok is a single
  constructor)
* `subst` via Eq.ndrec
* `rfl` for the final struct-projection reduction

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- The existential wrapper preserves the raw's structural dim:
when `inferRawCellGeneral? scope raw` accepts, the result's
stored `cellDimension` equals `raw.dim`.

First of three existential-variant soundness theorems.  Combined
with #168 (raw HEq) and #169 (HEq composition), this rules out
the wrapper laundering a different dim past the input. -/
theorem inferRawCellGeneral?_accepted_cellDimension_eq
    {profile : PolyProfile} {scope : Nat} {raw : RawCell scope}
    {result : CertifiedRawCellResult profile scope}
    (accepted :
      inferRawCellGeneral? scope raw = Except.ok result) :
    result.cellDimension = raw.dim := by
  rw [inferRawCellGeneral?] at accepted
  cases hCertify : certifyRawCellExact? (profile := profile) scope raw with
  | error rejection =>
      rw [hCertify] at accepted
      cases accepted
  | ok exactResult =>
      rw [hCertify] at accepted
      injection accepted with resultEq
      subst resultEq
      rfl

end LeanFX2.Foundation.PolyCell.Core
