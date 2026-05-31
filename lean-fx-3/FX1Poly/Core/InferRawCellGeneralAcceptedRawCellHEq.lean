import FX1Poly.Core.InferRawCellGeneral

/-! # InferRawCellGeneralAcceptedRawCellHEq — existential preserves rawCell

`inferRawCellGeneral?_accepted_rawCell_heq`: one of the
existential-variant soundness theorems for the ingress.  When the
existential wrapper accepts a raw input, the result's stored
`rawCell` field is heterogeneously equal to the input.

## Why HEq (not Eq)

The rawCell is un-indexed (`RawCell scope` for both the result's
field and the input), so an `Eq` would suffice type-theoretically —
but the HEq form is retained here for THREE reasons:

1. **API stability**: callers expecting `HEq result.rawCell raw`
   need no change.

2. **Composition**: the existential `_sound` theorem chains this HEq
   with the certified cell's raw-erasure HEq.  Keeping both legs at
   HEq avoids needing an Eq-to-HEq lift in the composition.

3. **Forward-compat**: future profiles with dim-1+ rawCells might
   re-introduce a dim index at the result type; if so, HEq stays
   the right API and no caller change is needed.

The Eq form is derivable as a one-liner corollary (`eq_of_heq`
applied to this theorem) when callers need it directly.

## The proof shape

Five steps:

1. Unfold `inferRawCellGeneral?` in the accepted hypothesis
2. Case on the underlying `certifyRawCellExact?` result
3. Error branch: contradiction via `cases accepted`
4. Ok branch: `injection`, `subst`, `rfl` closes the HEq goal
   (Lean's `rfl` tactic produces `HEq.refl _` when the two sides
   are definitionally equal — here `raw = raw` after subst).

## Zero-axiom verification

`rfl` for HEq closes by `HEq.refl _` when the types match
definitionally.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- The existential wrapper preserves the rawCell field as an HEq:
when `inferRawCellGeneral? scope raw` accepts, the result's stored
`rawCell` is heterogeneously equal to the input.

An existential-variant soundness theorem.  Combined with the
cellDimension-preservation and HEq-composition theorems, this rules
out the wrapper laundering a different raw past the input.

Note: under the un-indexed `RawCell scope`, both sides have the
same type, so this HEq is reducible to Eq — but HEq is kept for
API stability and to compose cleanly with the HEq-shape `_sound`
theorem. -/
theorem inferRawCellGeneral?_accepted_rawCell_heq
    {profile : PolyProfile} {scope : Nat} {raw : RawCell scope}
    {result : CertifiedRawCellResult profile scope}
    (accepted :
      inferRawCellGeneral? scope raw = Except.ok result) :
    HEq result.rawCell raw := by
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

end FX1Poly.Core
