import FX1Poly.Core.InferRawCellGeneral

/-! # InferRawCellGeneralAcceptedRawCellHEq — existential preserves rawCell

This file ships `inferRawCellGeneral?_accepted_rawCell_heq`: the
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

In v2, the rawCell is un-indexed (`RawCell scope` for both the
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

1. Unfold `inferRawCellGeneral?` in the accepted hypothesis
2. Case on the underlying `certifyRawCellExact?` result
3. Error branch: contradiction via `cases accepted`
4. Ok branch: `injection`, `subst`, `rfl` closes the HEq goal
   (Lean's `rfl` tactic produces `HEq.refl _` when the two sides
   are definitionally equal — here `raw = raw` after subst).

## Zero-axiom verification

Same tactics as #167; `rfl` for HEq closes by `HEq.refl _` when the
types match definitionally.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- The existential wrapper preserves the rawCell field as an HEq:
when `inferRawCellGeneral? scope raw` accepts, the result's stored
`rawCell` is heterogeneously equal to the input.

Second of three existential-variant soundness theorems.  Combined
with #167 (cellDimension preserves) and #169 (HEq composition),
this rules out the wrapper laundering a different raw past the
input.

Note: under v2's un-indexed `RawCell scope`, both sides have the
same type, so this HEq is reducible to Eq — but HEq is kept for
API compatibility with v1 and to compose cleanly with #169.  The
`_eq` companion below ships the tightened Eq form for v2-local
callers that want the structural equality directly. -/
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

/-- **V2-fix-7: tightened Eq companion.**

The HEq theorem above keeps the heterogeneous form for API
compatibility with v1.  Under v2's un-indexed `RawCell scope`,
both sides of the relation have the same type
(`RawCell scope`), so the relation collapses to definitional
Eq.

This `_eq` form is the v2-LOCAL companion: callers that already
operate within v2's un-indexed regime can use Eq directly without
needing `eq_of_heq` to lift the HEq form.

The HEq version composes cleanly with downstream HEq-shape
theorems (#169 sound, V2-bridge.* roundtrips that may
re-introduce a dim index).  This Eq version is the load-bearing
form for v2-only metatheory (subject reduction, confluence,
NbE -- all L3 tasks that stay in v2 throughout).

Proof: same structure as the HEq version; rfl closes because
result.rawCell evaluates to raw definitionally when the
certifier accepts. -/
theorem inferRawCellGeneral?_accepted_rawCell_eq
    {profile : PolyProfile} {scope : Nat} {raw : RawCell scope}
    {result : CertifiedRawCellResult profile scope}
    (accepted :
      inferRawCellGeneral? scope raw = Except.ok result) :
    result.rawCell = raw := by
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

/-- **V2-fix-7: HEq follows from Eq under same-type discipline.**

Demonstrates the relationship: the HEq theorem is derivable from
the Eq theorem via `heq_of_eq`.  This is the formal witness that
the HEq form is non-essential under v2's un-indexed regime.

In phase B of V2-mig (when v1 PolyTerm is fully retired and no
HEq composition with v1 is needed), the HEq form can be retired
in favor of the Eq form via this derivation. -/
theorem inferRawCellGeneral?_accepted_rawCell_heq_of_eq
    {profile : PolyProfile} {scope : Nat} {raw : RawCell scope}
    {result : CertifiedRawCellResult profile scope}
    (accepted :
      inferRawCellGeneral? scope raw = Except.ok result) :
    HEq result.rawCell raw :=
  heq_of_eq (inferRawCellGeneral?_accepted_rawCell_eq accepted)

end FX1Poly.Core
