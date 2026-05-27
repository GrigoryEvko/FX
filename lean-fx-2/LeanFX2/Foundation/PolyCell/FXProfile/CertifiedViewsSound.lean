import LeanFX2.Foundation.PolyCell.FXProfile.CertifiedViews
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactSound
import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactCompHRejects
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralAcceptedCellDimensionEq
import LeanFX2.Foundation.PolyCell.Core.InferRawCellGeneralSound

/-! # FXProfile/CertifiedViewsSound — FX-profile soundness suite

This file ships the soundness theorems for the FX-profile entry points
(#172).  Four theorems pin the FX-profile ingress to the same
no-laundering, dim-preservation, and compH-rejection guarantees that
the general v2 API enjoys (#165, #166, #167, #169).

Direct v2 counterpart to v1's soundness suite at
`Core/CertifyExact.lean:170-191` (`certifyFXCellExact?_sound`,
`_compH_rejects`, `certifyFXCell?_accepted_cellDimension_eq`,
`certifyFXCell?_sound`).

## The four theorems

* **`certifyFXCellExact?_compH_rejects`** — every horizontal
  composite rejects with `.unsupportedCompH`.  The single rejection
  class for the raw-indexed FX-profile ingress (Gray-tensor semantics
  pending Axis 6).

* **`certifyFXCellExact?_sound`** — every cell accepted by the
  raw-indexed FX ingress erases EXACTLY to its raw input.  The
  raw-indexed signature makes this trivial: `CertifiedRawCell`
  carries the input as a type-level parameter, so erasure
  back to that input is `rfl` (the architectural payoff of indexing
  by the EXACT input).

* **`certifyFXCell?_accepted_cellDimension_eq`** — every cell
  accepted by the existential FX ingress has its dim-erased
  `cellDimension` field equal to the input raw's computed `dim`.

* **`certifyFXCell?_sound`** — every cell accepted by the
  existential FX ingress has its certified cell's raw erasure
  heterogeneously equal to the input.  Combined with
  `_accepted_cellDimension_eq`, this closes the no-laundering
  guarantee on the existential ingress: no accepted cell can launder
  its raw cell or its dimension through the existential wrapper.

## Why all four are one-line delegations

`certifyFXCellExact?` is DEFINITIONALLY `certifyRawCellExact?
(profile := fxProfile)` and `certifyFXCell?` is DEFINITIONALLY
`inferRawCellGeneral? (profile := fxProfile)`.  Lean's definitional
reduction sees through these wrappers without an `unfold` or `rfl`
step.  So:

* A hypothesis `certifyFXCellExact? scope raw = Except.ok cell` is
  the SAME proposition as `certifyRawCellExact? (profile := fxProfile)
  scope raw = Except.ok cell`.
* A conclusion about the FX-profile result type is the SAME conclusion
  about the general result type with profile fixed.

The base theorems apply directly with `profile := fxProfile`
instantiated — no `by` block, no rewriting, no tactic combinators.
Each FX-profile theorem's body is a single base-theorem application.

This is the trust-cost-zero payoff of definitional wrappers: every
theorem on the underlying op transfers without a re-proof obligation.

## Together with the entry points (#172), this closes L1cert.4 soundness

#165-#169 ship the general no-laundering suite for the parameterized
infrastructure.  #172 ships the FX-profile entry-point wrappers.
This commit ships the soundness lift: same theorems re-stated against
the FX-profile names, with proofs by direct delegation.

The L1cert.4 soundness story is now complete for both API surfaces:
the general (profile-parameterized) and the FX-profile (profile-fixed).

## Zero-axiom verification

Each proof is a single function application against an already
audited zero-axiom theorem.  No new reasoning is introduced.  Audit
gates live in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.FXProfile

open Core

/-- The FX-profile raw-indexed certifier rejects horizontal composition
pending Gray-tensor semantics (Axis 6).

Direct delegation to `Core.certifyRawCellExact?_compH_rejects`
(#166) with `profile := fxProfile`.  The FX-profile call is
definitionally the general call with profile fixed, so the base
theorem applies without rewriting. -/
theorem certifyFXCellExact?_compH_rejects {scope : Nat}
    (leftOperand rightOperand : RawCell scope) :
    certifyFXCellExact? scope
        (.horizontalComposite leftOperand rightOperand) =
      Except.error .unsupportedCompH :=
  certifyRawCellExact?_compH_rejects (profile := fxProfile)
    leftOperand rightOperand

/-- Every cell accepted by the raw-indexed FX ingress erases exactly
to its raw input — the FX-level statement of no-false-positives for
`certifyFXCellExact?`.

Direct delegation to `Core.certifyRawCellExact?_sound` (#165).
The raw-indexed signature pins the input at the type level via
`CertifiedRawCell fxProfile scope rawCell`, so erasure back to the
input is `rfl` underneath. -/
theorem certifyFXCellExact?_sound {scope : Nat}
    {rawCell : RawCell scope}
    (certifiedCell : CertifiedRawCell fxProfile scope rawCell)
    (accepted :
      certifyFXCellExact? scope rawCell = Except.ok certifiedCell) :
    certifiedCell.certifiedCell.raw = rawCell :=
  certifyRawCellExact?_sound certifiedCell accepted

/-- Every cell accepted by the existential FX ingress recovers the
input's computed dimension — `result.cellDimension = raw.dim`.

Direct delegation to `Core.inferRawCellGeneral?_accepted_cellDimension_eq`
(#167).  The dim is the FIRST projection from the existential
wrapper; this theorem locks it to the input's computed dim, ruling
out dim-laundering through the type-erasure. -/
theorem certifyFXCell?_accepted_cellDimension_eq {scope : Nat}
    {raw : RawCell scope}
    {result : CertifiedRawCellResult fxProfile scope}
    (accepted : certifyFXCell? scope raw = Except.ok result) :
    result.cellDimension = raw.dim :=
  inferRawCellGeneral?_accepted_cellDimension_eq accepted

/-- Every cell accepted by the existential FX ingress has its
certified cell's raw erasure heterogeneously equal to the input —
the FX-level statement of no-false-positives for `certifyFXCell?`.

Direct delegation to `Core.inferRawCellGeneral?_sound` (#169).
The HEq form rather than Eq is forced by the existential wrapper:
`result.certifiedCell` has its rawCell as an existentialized index,
so the rawCell equality is across different types and HEq is the
canonical comparison form.

Combined with `_accepted_cellDimension_eq`, this closes the
no-laundering guarantee on the FX-profile existential ingress: no
accepted cell can launder its raw cell, its computed dimension, or
the agreement between them through the existential wrapper. -/
theorem certifyFXCell?_sound {scope : Nat}
    {raw : RawCell scope}
    {result : CertifiedRawCellResult fxProfile scope}
    (accepted : certifyFXCell? scope raw = Except.ok result) :
    HEq result.certifiedCell.raw raw :=
  inferRawCellGeneral?_sound accepted

end LeanFX2.Foundation.PolyCell.FXProfile
