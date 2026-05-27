import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralV2

/-! # InferRawCellGeneralV2AcceptedRawCellHEq — existential preserves rawCell

This file ships `inferRawCellGeneralV2?_accepted_rawCell_heq`: the
second of three existential-variant soundness theorems for the
ingress.  When the existential wrapper accepts a raw input, the
result's stored `rawCell` field is heterogeneously equal to the
input.

Direct v2 counterpart to v1's
`inferRawCellGeneral?_accepted_rawCell_heq`
(`Core/CertifyExact.lean:173`).

## Why HEq (not Eq), even though v2's rawCell is un-indexed

In v1, the existential wrapper erases the dim type index: the
result's `rawCell : PolyTerm profile cellDimension` is at the
EXISTENTIAL's `cellDimension`, not at the input's `dim`.  Even when
`cellDimension = dim` holds propositionally (via #167's analog),
the types of `result.rawCell` and `rawCell` differ until that
equation is `subst`'d.  HEq is the natural relation between values
at potentially-different types.

In v2, the rawCell is un-indexed (`RawCellV2 scope` for both the
result's field and the input).  An `Eq` would suffice
type-theoretically — but the HEq form is shipped here for THREE
reasons:

1. **API match with v1**: callers expecting `HEq result.rawCell raw`
   from v1 can use the v2 analog without changing their code.

2. **Composition with #169**: the existential `_sound` theorem
   (#169) chains this HEq with the certified cell's raw-erasure HEq.
   Keeping both legs at HEq avoids needing an Eq-to-HEq lift in the
   composition.

3. **Forward-compat**: future profiles with dim-1+ rawCells might
   re-introduce a dim index at the result type; if so, HEq stays
   the right API and no caller change is needed.

The Eq form is derivable as a one-liner corollary (`eq_of_heq`
applied to this theorem) when callers need it directly.

## The proof shape

Standard "executable-soundness" pattern from #167 — same skeleton,
different projection.  Five steps:

1. Unfold `inferRawCellGeneralV2?` in the accepted hypothesis
2. Case on the underlying `certifyRawCellExactV2?` result
3. Error branch: contradiction via `cases accepted`
4. Ok branch: `injection`, `subst`, `rfl` closes the HEq goal
   (Lean's `rfl` tactic produces `HEq.refl _` when the two sides
   are definitionally equal — here `raw = raw` after subst).

## Zero-axiom verification

Same tactics as #167; `rfl` for HEq closes by `HEq.refl _` when the
types match definitionally.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- The existential wrapper preserves the rawCell field as an HEq:
when `inferRawCellGeneralV2? scope raw` accepts, the result's stored
`rawCell` is heterogeneously equal to the input.

Second of three existential-variant soundness theorems.  Combined
with #167 (cellDimension preserves) and #169 (HEq composition),
this rules out the wrapper laundering a different raw past the
input.

Note: under v2's un-indexed `RawCellV2 scope`, both sides have the
same type, so this HEq is reducible to Eq — but HEq is kept for
API compatibility with v1 and to compose cleanly with #169. -/
theorem inferRawCellGeneralV2?_accepted_rawCell_heq
    {profile : PolyProfile} {scope : Nat} {raw : RawCellV2 scope}
    {result : CertifiedRawCellResultV2 profile scope}
    (accepted :
      inferRawCellGeneralV2? scope raw = Except.ok result) :
    HEq result.rawCell raw := by
  rw [inferRawCellGeneralV2?] at accepted
  cases hCertify : certifyRawCellExactV2? (profile := profile) scope raw with
  | error rejection =>
      rw [hCertify] at accepted
      cases accepted
  | ok exactResult =>
      rw [hCertify] at accepted
      injection accepted with resultEq
      subst resultEq
      rfl

end LeanFX2.Foundation.PolyCell.Core
